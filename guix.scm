(use-modules
 (guix packages)
 (gnu packages coq))

(concatenate-manifests
 (list
  (package->development-manifest coq)
  (package->development-manifest coq-ide)))
