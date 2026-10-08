+++
id = "rem-pur-status-after-completion"
kind = "remark"
title = "Dependency order of the smooth-purity proof"
order = 2037
uses = ["cor-amb-affine-space-adjunction", "cor-pur-vector-bundle-purity", "lem-pur-smb-extraordinary", "prop-asd-smooth-base-change", "thm-amb-p1-adjunction", "thm-amb-vector-bundle-purity", "thm-asd-smooth-tensor", "thm-pur-cohomological-smoothness", "thm-pur-diagonal-dualizing-object", "thm-pur-dnc-invariance", "thm-pur-finite-coefficient-smooth-purity", "thm-pur-smooth-base-change-coherence"]
+++
The independent starting point is the projective-line adjunction
[thm-amb-p1-adjunction], whose two triangles are computed from
the two integrals of the Cartier diagonal class. It gives
[cor-amb-affine-space-adjunction], and then the orientation-free
tensor and base-change statements
[thm-asd-smooth-tensor], [prop-asd-smooth-base-change] and the
vector-bundle orientation [thm-amb-vector-bundle-purity].
Their finite etale-origin transports are
[thm-pur-cohomological-smoothness], [lem-pur-smb-extraordinary], [cor-pur-vector-bundle-purity].
Only after these inputs does the deformation statement
[thm-pur-dnc-invariance] identify the section invariants, leading
to [thm-pur-diagonal-dualizing-object] and
[thm-pur-finite-coefficient-smooth-purity].
The coherence of this chosen orientation is the later conclusion
[thm-pur-smooth-base-change-coherence]; it is not an input to
affine-line purity or orientation-free exceptional base change.
This dependency order does not infer any theorem from a package
summary or certify the separate proofs of the optional Thom route.
