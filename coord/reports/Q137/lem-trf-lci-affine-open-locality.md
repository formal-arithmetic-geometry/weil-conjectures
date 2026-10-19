## Worker report

The project already contains the exact statement declaration
`AlgebraicGeometry.lci_affine_open_locality` in
`Sheaf.TraceFormula.LciAffineOpenLocality` (`lean/Sheaf/TraceFormula/LciAffineOpenLocality.lean`).
I copied that module into this packet and retained its theorem statement with `sorry`; the
node record is attributed to Q137 on the UTC delivery date. The declaration has
`set_option autoImplicit false`, explicitly binds the universe `u`, and compiles cleanly
with the required wrapper.

The Lean rendering follows the node clause by clause:

* `k : Type u` with `[Field k]` is the field hypothesis.
* `Z : Scheme.{u}` and `s : Z ⟶ Spec (.of k)` are the scheme and its structure morphism.
* `hcover` existentially binds `I : Type u`, `C : I → CommRingCat.{u}`, the algebra
  structures `aC : ∀ i, Algebra k (C i)`, finite-type instances `ftC`, and chart maps
  `φ : ∀ i, Spec (C i) ⟶ Z`.
* The first cover conjunct is `∀ i, IsOpenImmersion (φ i)`.
* The second is the required compatibility
  `φ i ≫ s = Spec.map (CommRingCat.ofHom (@algebraMap k (C i) _ _ (aC i)))`.
* The third is pointwise coverage, `∀ z : Z, ∃ i, ∃ x : Spec (C i), φ i x = z`.
* The fourth requires each chart algebra to satisfy
  `@Algebra.IsLocalCompleteIntersection k (C i) _ _ (aC i) (ftC i)`.
* The conclusion quantifies `W : Z.Opens` and `IsAffineOpen W`, then supplies the finite-type
  witness `ftW` for the canonical algebra map
  `(((Scheme.ΓSpecIso (.of k)).inv ≫ s.appLE ⊤ W le_top).hom.toAlgebra)` on
  `Γ(Z, W)`, and asserts `Algebra.IsLocalCompleteIntersection` for that same structure.

The dependency `def-pc-scheme` is the Mathlib declaration `AlgebraicGeometry.Scheme`.
The dependency `def-weil-pbc-complete-intersection-over-field` is imported through
`Sheaf.RingTheory.CompleteIntersectionOverField`, using
`Algebra.IsLocalCompleteIntersection` (and its finite-type witness parameter) exactly as
recorded by that node. No private replacement is introduced.

I checked the empty-cover/empty-scheme and zero-coordinate-ring conventions: the statement
allows an empty index type and an affine open with the zero section ring, while the finite-type
witness and the recorded complete-intersection predicate remain explicit. The universe of the
cover index and chart rings is the scheme universe `u`, so no smaller independent universe is
introduced.

Searches performed:

* `msearch.py ... leanfinder "local complete intersection coordinate algebra every affine open scheme over a field"` returned only affine-cover, smoothness, and finite-type declarations; no matching theorem.
* `msearch.py ... loogle "Algebra.IsLocalCompleteIntersection, IsAffineOpen, Scheme.Γ"` returned no hits (the project predicate is not Mathlib).
* `msearch.py ... grep "lci_affine_open_locality|IsLocalCompleteIntersection" Sheaf` found the existing project module and related complete-intersection modules.
* `rg` over `WeilConjectures/` and project `lean/Sheaf` found no upstream duplicate; the exact project declaration is the module recorded above.
* Existing node searches and the recorded dependency records were inspected; no new node or dependency repair is needed.

The copied module was compiled with
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q137 lem-trf-lci-affine-open-locality lean/Sheaf/TraceFormula/LciAffineOpenLocality.lean` and produced no errors or non-sorry warnings.

## Second reading by Q137

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
