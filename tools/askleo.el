;; Invocation of Leo2 from Emacs
;; Nik Sultana, Sept 2012, Free University Berlin
;;
;; Depends on $LEO2 envir variable, which must point to
;; Leo2's root directory.
;;
;; TODO
;; * add send-whole-buffer-and-run mode
;; * colour script and output differently
;; * picking out errors, exceptions, warnings, etc


;;  Consts and vars

(defconst askleoK "askleo"
  "Default Askleo buffer name")
(let ((raw_leo2_path (shell-command-to-string "echo $LEO2")))
  (defvar askleo-leo2_path (substring raw_leo2_path 0
                                  (- (length raw_leo2_path) 1))
    "Path to Leo2"))
(defvar askleo-path (concat askleo-leo2_path "/tools/askleo")
  "Location of the Askleo executable")
(defvar askleo-args "" ;FIXME check how to change within emacs
  "Arguments that the Askleo script gives to Leo2")


;FIXME make fonts work with different types (e.g. "tty"),
;classes (e.g. "color") etc (e.g. "background dark")
(setq askleo-font-info
      `((t (:foreground "yellow" :background "black"))))
(setq askleo-font-eureka
      `((t (:foreground "green"))))
(setq askleo-font-szs
      `((t (:foreground "red" :background "yellow"))))
(setq askleo-font-stars
      `((t (:foreground "blue"))))
(setq askleo-font-prefix
      `((t (:foreground "orange"))))
(setq askleo-font-subproblem
      `((t (:foreground "orange" :background "light blue"))))
(setq askleo-font-timings
      `((t (:foreground "black" :background "light blue"))))

;FIXME make defvar
(setq askleo-highlights
      ;FIXME pick appropriate colours
  '(("SZS status \\w+" . askleo-font-szs)
    ("Eureka" . askleo-font-eureka)
    ("\*.*" . askleo-font-stars)
    ("^# " . askleo-font-info)
    ("LEO-II: " . askleo-font-prefix)
    ("^([0-9]+) Problem:" . askleo-font-subproblem)
    ("^[0-9]+.[0-9]+:" . askleo-font-timings)))

(defvar askleo-syntax-table nil)
(setq askleo-syntax-table
      (let ((synTable (make-syntax-table)))
        (modify-syntax-entry ?% "< b" synTable)
        (modify-syntax-entry ?\n "> b" synTable)
        synTable))

(defun tptp-comment-dwim (arg)
  "Comment/uncomment TPTP lines"
  (interactive "*P")
  (require 'newcomment)
  (let ((comment-start "%") (comment-end ""))
    (comment-dwim arg)))

(define-derived-mode askleo-mode fundamental-mode
  "Major mode for editing Leo2 input and viewing its output"
  :syntax-table askleo-syntax-table
  (setq font-lock-defaults '(askleo-highlights))
  (setq mode-name "Askleo")
  (define-key askleo-mode-map [remap comment-dwim] 'tptp-comment-dwim))


;; Startup check

(if (equal askleo-leo2_path "")
  (error "Askleo: $LEO2 environment variable not set")
  (message (concat "Askleo: $LEO2 is " askleo-leo2_path)))


;; Functions

(defun askleo-start ()
  "Start Leo2 listener"
  (interactive)
  ;FIXME check if already started, otherwise could get confusing
  (start-process askleoK askleoK askleo-path askleo-args)
  ;FIXME switch the askleo buffer to use the askleo mode
  (message "Started Askleo"))

(defun askleo-send (start end)
  "Send region to Leo2 listener's buffer"
  (interactive "r")
  ;FIXME check that listener has been started
  (append-to-buffer (get-buffer askleoK) start end) ;FIXME this being shown after Leo2 output
  (process-send-region (get-process askleoK) start end)
  (message "Sent to Askleo"))

(defun askleo-do ()
  "Run Leo on the buffered input"
  (interactive)
  ;FIXME check that listener has been started
  (process-send-eof askleoK)
  (message "Ran Leo on buffered input"))

(defun askleo-startsenddo (start end)
  "Run Leo2 on a region"
  (interactive "r")
  (askleo-start)
  (askleo-send start end)
  (askleo-do))

(defun askleo-clear ()
  (interactive)
  "Clear the Askleo buffer"
  (message "Clearing Askleo buffer")
  ;FIXME no need for -other-window -- just clear the buffer in the background
  ;FIXME also, misbehaves if we're already in the askleo buffer.
  (switch-to-buffer-other-window (get-buffer askleoK))
  (erase-buffer))

(defun askleo-kill ()
  (interactive)
  "Kills the Leo2 process"
  (message "Killed Askleo")
  (kill-process (get-process askleoK)))


;; Bindings

(global-set-key "\C-c\C-l" 'askleo-start)
(global-set-key "\C-c\C-s" 'askleo-send)
(global-set-key "\C-c\C-a" 'askleo-do)
(global-set-key "\C-c\C-k" 'askleo-kill)
(global-set-key "\C-c\C-c" 'askleo-clear)
(global-set-key "\C-c\C-e" 'askleo-startsenddo)


(provide 'askleo-mode)