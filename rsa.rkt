# RSA
#An RSA encryptor and decryptor that works for text and numbers.
;;
;;*****************************************
;; Vibhanshu Bhardwaj
;; University of Waterloo
;; 'Random-key' RSA encryptor and decryptor.
;;*****************************************
;;


(require racket/match)


;;(prime-list-generator n) generates a list of primes that are
;; smaller than n.
;;prime-list-generator: Nat -> (listof Nat)
;; requires: n > 2
;:Examples:
(check-expect (prime-list-generator 3) '(2))
(check-expect (prime-list-generator 4) '(2 3))
(check-expect (prime-list-generator 5) '(2 3))

(define (prime-list-generator n)
  (local
    
    ;;(divides? x y) determines if x is a factor of y
    ;;divides?: Num Num -> Bool   
    [(define (divides? x y)
       (zero? (modulo x y)))
     
     ;;(make-list start end) creates a list of numbers from start to end.
     ;; make-list: Nat Nat -> (listof Nat)
     (define (make-list start end)
       (cond
         [(= start n) empty]
         [else (cons start (make-list (add1 start) end))]))
     
     ;; list-of-nat is the list of numbers from 2 to n because
     ;; we're only concerned with primes.
     (define list-of-nat (make-list 2 n))
     
     ;;(multiple-remover i lonat) removes all multiples of i from lonat
     ;;multiple-remover: Nat -> (listof Nat)
     (define (multiple-remover i lonat)
       (filter (λ (x) (not (divides? x i))) lonat))
     
     ;;(composite-remover lonat) removes all composite numbers
     ;; from lonat so that it only contains primes. It uses the result
     ;;"to determine if a number is prime, check if it has factors
     ;; smaller than its squareroot.
     ;;composite-remover: (listof Nat) -> (listof Nat)
     (define (composite-remover lonat)
       (cond
         [(> (sqr (first lonat)) n) lonat]
         [else (cons (first lonat) (composite-remover
                                    (multiple-remover (first lonat)
                                                      (rest lonat))))]))]
    
    (composite-remover list-of-nat))) ;main function body



;;Tests:
(check-expect (prime-list-generator 10) '(2 3 5 7))
(check-expect (prime-list-generator 17) '(2 3 5 7 11 13))


(define prime-list (prime-list-generator 100000))
;;all the primes will be selected from prime-list.


(define p (list-ref prime-list (random (length prime-list))))
;first prime (p) in RSA


;;(unique-selector selected-value original-value) makes sure
;; that the picked selected-value is not the same as original-value.
;(unique-selector: Nat Nat -> Nat
;;Tested in main tests.

(define (unique-selector selected-value original-value)
  (cond
    ;if they're same, pick another value. This will happen very rarely.
    [(= selected-value original-value)
     (unique-selector (list-ref prime-list (random (length prime-list)))
                      original-value)]
    [else selected-value]))

;;Manual Test for the case when the 2 values are equal
(check-expect  (= (unique-selector 5 5) 20) false)


(define q (unique-selector
           ;this ensures p!=q
           (list-ref prime-list (random (length prime-list))) p))
;second prime (q) in RSA.

(define n (* p q))
; n of RSA

(define phi-function (* (- p 1) (- q 1)))
;The Phi(n) of RSA

;;(ensure-gcd-1 x y) ensures gcd of x and y is 1
;; by randomly choosing values of y.
;;ensure-gcd-1: Nat Nat -> Nat
;;Examples:
(check-expect (gcd 4 (ensure-gcd-1 4 8)) 1)
(check-expect (gcd 4 (ensure-gcd-1 4 9)) 1)
(check-expect (gcd 100 (ensure-gcd-1 100 10)) 1)

(define (ensure-gcd-1 x y)
  (cond
    [(= 1 (gcd x y)) y]
    [else (ensure-gcd-1 x (random 4294967087))])) ;random's upper limit.

;;Tests:
(check-expect (gcd 3 (ensure-gcd-1 3 5)) 1)
(check-expect (gcd 4 (ensure-gcd-1 4 11)) 1)
(check-expect (gcd 3 (ensure-gcd-1 3 3)) 1)


(define public-key (ensure-gcd-1 phi-function (random 4294967087)))
;;Public key (e) and phi(n) must have gcd 1. We picked public-key
;; such that gcd (e, phi(n)) = 1


;;(extended-euclid-algo given-list) applies Extended Euclidean Algo to
;; relevant elements of elements of given-list.
;;(extended-euclid-algo: (list (listof Int) (listof Int)) -> (listof Int)
;;Examples:
;;tested in the final function's body.

(define (extended-euclid-algo given-list)
  (match given-list
    [(list (list a b r q) (list A B R Q))
     (cond
       [(= 0 R) (list a b r q)] ;the previous is the answer row
       [else
        ;;now we'll calculate new a,b,r,q for the recursive step.
        ;; see wikipidea of EEA for why.
        (let*
            ([newq (quotient r R)] 
             [newa (- a (* newq A))]
             [newb (- b (* newq B))]
             [newr (- r (* newq R))])
          (extended-euclid-algo
           (list (list A B R Q)(list newa newb newr newq))))])]))


(define private-key (modulo 
                     (first (extended-euclid-algo
                             (list (list 1 0 public-key 0)
                                   (list 0 1 phi-function 0)))) 
                     phi-function))
;;Calculation of private key according to RSA.


;;(exp-modulo message publick-key n) computes (modulo (message^public-key) n
;; it's a faster way to compute the cipher text using properties of congruence.
;;exp-modulo: Nat Nat Nat -> Nat.
;;Examples:
;;Tested in the encryption and decryption combined tests.

(define (exp-modulo message public-key n)
  (cond 
    [(= public-key 1) (modulo message n)]
    [(odd? public-key) (modulo (* (exp-modulo (modulo (sqr message) n)
                                              (quotient public-key 2) n)
                                  message) n)]
    [(even? public-key) (exp-modulo (modulo (sqr message) n)
                                    (quotient public-key 2) n)]))

;;(encrypt-message message) encrypts message into a cipher text.
;;encrypt-message: Nat -> Nat.
;; requires: message > 2
;;Examples and Tests in the combined decrypt and encrypt tests.

(define (encrypt-message message)
  (exp-modulo message public-key n))

;;(decrypt-cipher cipher) decrypts cipher into the original message.
;;decrypt-cipher: Nat -> Nat.
;;Examples and Tests in the combined decrypt and encrypt tests.

(define (decrypt-cipher cipher)
  (exp-modulo cipher private-key n))



;;Combined Tests for decryption and encryption.

(check-expect (decrypt-cipher
               (encrypt-message 240)) 240)
(check-expect (decrypt-cipher
               (encrypt-message 2)) 2)
(check-expect (decrypt-cipher
               (encrypt-message 10000000)) 10000000)





;;;;;;;;;;;;;;;;;;Encryption and Decryption of Strings.;;;;;;;;;;;;;;;;;;





;;(ecnrypt string) encrypts string according to RSA.
;;encrypt: Str -> (listof Int)
;;Tested in the combined tests for encryption and decryption.
(define (encrypt string)
  (local
    
    ;;(string->loint str) converts str to a list of integers (ASCII value)
    ;;string->loint: Str -> (listof Int)    
    [(define (string->loint str)
       (local
         [(define mylist (string->list str))
          
          ;;(lochar->loint given-list) converts given-list
          ;; to list of integers (ASCII value).
          ;;lochar->loint: (listof Char) ->(listof Int)
          (define (lochar->loint given-list)      
            (map char->integer given-list))]
         
         (lochar->loint mylist)))
     
     (define loint (string->loint string))

     ;;(encrypt-loint my-loint) encrypts each element of my-loint
     ;; that is, it converts messages to cipher text.
     ;;encrypt-loint: (listof Int) -> (listof Int)
     (define (encrypt-loint my-loint)     
       (map encrypt-message my-loint))]
    (encrypt-loint loint)))

  
;;(decrypt loint) decrypts loint.
;;decrypt: (listof Int) -> Str
;;Tested in the combined tests for encryption and decryption.
(define (decrypt loint)
  (local
    ;;(decrypt-loint loint) decrypts each element of loint.
    ;; that is, it decyrpts ciphers.
    ;;decrypt: (listof Int) -> (listof Int)
    [(define (decrypt-loint loint)
       (map decrypt-cipher loint))

     ;;(loint->lochar loint) converts each ASCII integer in loint
     ;; to its character.
     ;;loint->lochar: (listof Int) -> (listof Char)
     (define (loint->lochar loint)
       (map integer->char loint))]
    
    (list->string (loint->lochar (decrypt-loint loint)))))



;;Testing of encrypt and decrypt.

(check-expect (decrypt (encrypt "lion")) "lion")
(check-expect (decrypt (encrypt "")) "")
(check-expect (decrypt (encrypt "Why is Dave Tompkins' class not open?"))
              "Why is Dave Tompkins' class not open?")
(check-expect (decrypt (encrypt "abcdefghijklmnopqrstuvwxyz"))
              "abcdefghijklmnopqrstuvwxyz")


     
     
     
     
