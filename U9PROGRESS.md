
2026-11-05 K6 initial source review:
- Read Lean skill, performance guide, blueprint lem-pur-a1-direct-image and PR #2071/#2088.
- PR #2071 at bb375e28e supplies a full-looking reduction: condensed constant case,
  pro-etale local lisse case, truncation devissage, Noetherian induction, reduction of X.
- Merging #2071 as requested. Resolve AffineLineBundle by retaining current adjunction and
  twist declarations, importing HomotopyInvariance, and taking #2071's exact unit proof.
- Retain current FourierInversion/OtherSections proof: the branch version would replace
  the already-proved Thom isomorphism with a sorry. No declaration statements changed.
- #2088 adds a new trace sorry and removes existing purity declarations; do not merge it,
  since the homotopy-invariance work it contains is already in #2071.
- Next: inspect imported proofs and dependencies, then ucheck the leaf and all merged modules.
