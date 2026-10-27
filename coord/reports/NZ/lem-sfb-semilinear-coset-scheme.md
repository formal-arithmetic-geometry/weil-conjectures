## Worker report

The module `Sheaf.AlgebraicGeometry.SemilinearCosetScheme` states
`AlgebraicGeometry.semilinear_coset_scheme`. Its only theorem has proof `sorry`.
There are no new definitions, added nodes, dependency repairs or statement corrections.
The original node is copied with only `lean` changed.

Source read: ILO, Travaux de Gabber, Expose X 2.3 Step 2, printed pp. 150–151
(PDF pages 156–157). The source describes contracted products and the extension
of (2.a) to (2.b). The node explicitly expands that construction into left actions
and arbitrary semilinear coset coproducts. The docstring records all seven steps
of the node's proof, including descent, uniqueness, base change and the orbit argument.

Hypothesis correspondence:

- Fields e contained in K: `(e K : Type u) [Field e] [Field K] [Algebra e K]`.
  The inclusion is `algebraMap e K`, injective because e is a field.
- Finite group and e-linear field action: `(G : Type v) [Group G] [Finite G]`
  and `pi : G →* (K ≃ₐ[e] K)`; subgroup: `Gamma : Subgroup G`.
- K-scheme W: `W : Scheme.{u}` and `p : W ⟶ Spec (.of K)`.
- Left Gamma-action: `d : Gamma →* Aut W`; Mathlib's multiplication of
  automorphisms is composition in the left-action order.
- Scalar compatibility: `hd`, with `(pi (gamma : G)⁻¹).toRingHom`.
  A homomorphism preserves inverses, so this is precisely pi(gamma) inverse.
  Lean's `≫` writes the diagram in the reverse order from ordinary function composition.
- e-scheme B: `B : Scheme.{u}` and `b : B ⟶ Spec (.of e)`.
- Gamma-invariant e-morphism q: `q`, `hqbase` and `hq`.
- Any normalized representatives: `s : G ⧸ Gamma → G`, `hs` and `hsone`.
  `QuotientGroup.leftRel` defines left cosets for an arbitrary, possibly nonnormal subgroup.

Conclusion correspondence, in its Lean order:

- The existential `Y, pY, t, a, f` gives the K-scheme, maps for EVERY g,
  genuine left action and map to B. Existential `htf` is the fourth displayed
  identity, and `haf` gives G-invariance. These are bound proof witnesses because
  canonical pullback maps below depend on their commutative-square proofs.
- `Nonempty (IsColimit (Cofan.mk Y ...))` gives the coproduct universal property
  for the maps indexed by s, without choosing a particular coproduct implementation.
- `IsOpenImmersion`, `IsClopen (Set.range ...)`, the `Disjoint` clause for distinct
  cosets, and `∀ y, ∃ c w, ...` give exactly the open, closed, disjoint and covering
  assertions on the underlying topological images.
- The next three clauses give `t (g * gamma) = (d gamma).hom ≫ t g`,
  `t g ≫ pY = p ≫ Spec.map ...`, and `t g ≫ (a h).hom = t (h * g)`.
  Together with `htf` these are all four displayed defining identities.
- The next scalar clause gives semilinearity of a; `f ≫ b = pY ≫ Spec.map ...`
  gives the assertion that f is an e-morphism; its invariance is already `haf`.
- The quantified `Z, k` clause gives `∃! l, ∀ g, t g ≫ l = k g` for each family
  satisfying the contracted-product relation. This is the relation's mapping
  property explicitly spelled out by proof step 5, not a claim about a point-set
  quotient replacing the scheme construction.
- The `s', Y', pY', t', a', f'` clause compares any second representative
  construction with the same defining identities. It provides `phi : Y ≅ Y'`
  preserving every t_g, the scalar map, f and the group action. These compatibility
  equations express “preserving all these maps.” No arbitrary isomorphism is substituted.
- For EVERY `T : Scheme.{u}` and `z : T ⟶ B`, the next `IsColimit` clause uses
  `pullback.map q z f z (t (s c)) (𝟙 T) (𝟙 B)` as the actual base-changed
  coprojections; hence Y_T is the coproduct of copies of W_T as specified.
- The last clause is the implication from nonempty single Gamma-orbit to
  nonempty single G-orbit. `Nonempty ↥(pullback ...)` means nonempty underlying
  points, and `∀ x y, ∃ gamma/h, pullback.map ... x = y` means precisely one orbit.
  The actions are induced by the ORIGINAL d and a, with identities on T and B.
  They are not arbitrary actions or actions on field-valued lifts.
- The node's negative qualifications are honored: there is no normality,
  finiteness, separability or Galois assumption on K/e; no finite-type or
  separatedness assumption on W or B; no scheme quotient-existence assumption.

Dependency declarations read and used:

- `def-weil-field`: Mathlib `Field`, `Mathlib.Algebra.Field.Defs`.
- `def-pc-field-extension`: `Algebra`, `Mathlib.Algebra.Algebra.Defs`.
- `def-pc-scheme` and `def-weil-affine-spectrum`: `AlgebraicGeometry.Scheme`,
  `Scheme.Hom`, `Spec`, `Spec.map`, `Mathlib.AlgebraicGeometry.Scheme`.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `.fst`, `.snd`, `.map`,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion`,
  `Mathlib.AlgebraicGeometry.OpenImmersion`.
- `lem-weil-pbc-scheme-coproduct-family`: its Mathlib match supplies existence,
  `AlgebraicGeometry.sigmaOpenCover`, and `disjoint_opensRange_sigmaι`, in
  `Mathlib.AlgebraicGeometry.Limits`; the target is expressed with `Cofan.mk`
  and `IsColimit`, exactly the universal property of that match. It needs no repair.
- Proof dependency `lem-weil-pbc-sets-etale-inverse-image-constant-base-change`:
  `AlgebraicGeometry.baseChange_sigmaScheme_iso`,
  `Sheaf.Paper.SetsEtaleInverseImageConstantBaseChange`, imported without `public`.
  Its full signature and docstring were read. Other proof dependencies are already
  available through the public statement imports. The upstream compact-object
  example and its current node record were also read (the old Sheaf file is withdrawn).

All statement types are from public Mathlib imports; the private proof import
is not needed to expose their interfaces. Universes u and v and all binders are
explicit, with `set_option autoImplicit false`. The finite group can lie in any
universe v, independently of schemes u: only its finite coset family is needed,
and the conclusion uses a cocone rather than demanding an extraneous `Small` binder.

Edge cases checked before writing:

- W empty: every copy and Y are empty; the orbit premise is false, and neither
  covering nor uniqueness forces a point. T empty behaves in the same way.
- Gamma trivial: Y is the coset-indexed sum with no nontrivial relations.
- Gamma = G: the quotient has one element, normalized representative 1,
  Y is W and all t_g are d_g; none of the clopen/disjoint assertions excludes it.
- G trivial, trivial pi and nonfaithful pi/d: all are included.
- Arbitrary characteristic and infinite/non-normal K/e are allowed.
- Nonnormal Gamma uses a left-coset SET only; no quotient-group instance is used.
- T may be nonreduced or non-affine. Orbit quantifiers are over all points of
  the pullback scheme, not only rational or geometric lifts.
- The order t_(g gamma) = t_g composed with d_gamma and Spec(pi(g) inverse)
  agrees with the source proof's S_(gh) = S_g composed with S_h convention.

Searches (all msearch calls used the assigned NZ/item identifiers):

- LeanFinder: “Induction of semilinear subgroup actions on schemes by coproduct
  over left cosets, with invariant map and transitive base change.” Eight hits,
  chiefly `Rep.indToCoindAux`, representation induction, subgroup transversals;
  none states the scheme construction.
- LeanSearch: “A semilinear scheme action induced from a subgroup is a coproduct
  indexed by left cosets.” Eight hits, including quotient actions/transitivity,
  subgroup transversals and `Representation.ofQuotient`; no scheme induction.
- Loogle: initial compound query `CategoryTheory.Action, QuotientGroup,
  AlgebraicGeometry.sigmaOpenCover` failed identifier resolution. Repeated with
  `AlgebraicGeometry.sigmaOpenCover`: four hits, the cover and its projection
  formulas in `Mathlib.AlgebraicGeometry.Limits`; these are ingredients only.
- Mathlib grep via msearch: `semilinear|contractedProduct|coset` in
  AlgebraicGeometry: four hits, all structure-sheaf semilinear maps.
- rg of `lean/WeilConjectures` and `lean/Sheaf`: semilinear/contracted-product/coset
  searches found many coefficient and torsor constructions, plus
  `CommonFieldSemilinearInduction`. The latter's complete signature was read:
  it is a downstream finite-family common-normal-field existence theorem,
  not induction for the arbitrary given K/e, subgroup and W here. It cannot
  replace this node and is deliberately not imported (avoiding a dependency cycle).
- rg for the exact item id in `lean/WeilConjectures` found no match.
- rg for the new declaration/module name and semilinear-coset phrases in
  `dag/lean_names_upstream.json`, `lean/Sheaf` and `lean/WeilConjectures` found
  only the downstream common-field narrative; no name collision.

Validation: prescribed scompile.py compiled both the sandbox probe and the
library module on the live server (1.6 s and 1.7 s); no errors or unexpected warnings.
No shared source was edited and no direct Git or global build command was run.

## Second reading by NZ

Author's separate rereading, not an independent agent review (the dispatcher
forbids starting agents; independent review is the maintainer's). Reopened the
node statement and complete module after compilation. Checked the binders e,K,
G,pi,Gamma,W,p,d,B,b,q and both representative hypotheses against each phrase.
Checked each of the four t identities, the colimit, all four topological cover
properties, the mapping property, preservation of t/pY/f/a by phi, semilinearity,
e-linearity, invariance, arbitrary T base change, and BOTH nonemptiness and
transitivity on underlying points. Verified pullback.map's square orientation
from its Mathlib signature: htf, hq and haf occur symmetrically because that API
asks q = t_g followed by f and q = d_gamma followed by q. All clauses match;
no statement correction or discrepancy found. No theorem proof other than
`sorry` and no additional helper notion were introduced.
