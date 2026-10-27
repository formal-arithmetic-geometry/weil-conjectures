## Worker report

The module `Sheaf.AlgebraicGeometry.FieldBasePointFibreIsomorphism` states
`AlgebraicGeometry.Scheme.fieldBasePoint_fibre_isomorphism`. Its only theorem has
proof `sorry`. No definitions, new nodes, dependency repairs, or statement
corrections are needed. The live node has a reviewed stage-1 split and no Lean
record; this delivery adds its stage-2 record without re-splitting it. The previous
worker's stale-stage-1-assignment refusal does not apply to adding this statement.

Read the node, every statement dependency and its recorded declaration/docstring,
and the three additional Mathlib proof-dependency interfaces. Read the source
passage in `literature/stacks-project/morphisms.tex`, Tag 03J5, proof of (1) implies
(2), especially the formula identifying a field-valued pullback with extension of
the residue fibre. The auxiliary canonical field-base identification is proved
in the node by the residue-field comparison and the pullback universal property.
The theorem docstring records all four proof steps and their dependencies.

Hypothesis and clause correspondence:

- A field K: `(K : Type u) [Field K]`. Its spectrum S is always the actual
  `Spec (CommRingCat.of K)`, using def-weil-affine-spectrum and def-pc-scheme.
- Its unique point ξ = (0): `(ξ : Spec (CommRingCat.of K))`. A field spectrum has
  exactly one point, so quantifying over ξ is equivalent to choosing that point.
  No prime-ideal hypothesis or extra choice of a field embedding is introduced.
- L is the scheme residue field: `(Spec (CommRingCat.of K)).residueField ξ`, using
  the recorded def-weil-residue-field interface, rather than the prime ideal's
  residue field as a substitute.
- The canonical germ-residue map φ: the first existential witness is an isomorphism
  `e : CommRingCat.of K ≅ (Spec (CommRingCat.of K)).residueField ξ`, with
  `e.hom = (ΓSpecIso (CommRingCat.of K)).inv ≫
  (Spec (CommRingCat.of K)).Γevaluation ξ`. Here Γevaluation is defined to be the
  germ on the top open followed by the residue map. Thus the isomorphism has the
  prescribed forward field map, not an arbitrary isomorphism between the fields.
- The canonical residue morphism jξ is Spec(φ) and an isomorphism: the witness
  `j : Spec L ≅ Spec K` has both
  `j.hom = (Spec (CommRingCat.of K)).fromSpecResidueField ξ` and
  `j.hom = Spec.map e.hom`. The direction is contravariant, as required.
- Its global-section map is φ under affine identifications: the fourth conjunct
  is `(ΓSpecIso K).inv ≫ j.hom.appTop ≫ (ΓSpecIso L).hom = e.hom`, with the
  bundled rings written out in the actual signature. It first identifies K with
  Γ(S), applies the global-section map, then identifies Γ(Spec L) with L.
- Every W and h: `∀ (W : Scheme.{u}) (h : W ⟶ Spec (CommRingCat.of K))`.
  No affineness, nonemptiness, finiteness, reducedness or characteristic condition
  on W or K is assumed.
- The chosen scheme-theoretic fibre F and projections: `h.fiber ξ`, `h.fiberι ξ`,
  and `h.fiberToSpecResidueField ξ` are exactly the recorded def-pc-scheme-fibre
  declarations. They are the chosen pullback of h and the canonical residue map.
- The first projection is invertible: `IsIso (h.fiberι ξ)`.
- The square commutes: `h.fiberι ξ ≫ h = h.fiberToSpecResidueField ξ ≫
  (Spec (CommRingCat.of K)).fromSpecResidueField ξ`. This clause is included
  because the node explicitly asserts it.
- The formula for the second projection: `h.fiberToSpecResidueField ξ =
  h.fiberι ξ ≫ h ≫ j.inv`. Categorical composition writes the rightmost
  mathematical composite first, so this is q = jξ⁻¹ ∘ h ∘ p.
- Every choice of fibre product: the statement quantifies over F, p and q and
  assumes `IsPullback p q h ((Spec (CommRingCat.of K)).fromSpecResidueField ξ)`.
  This is precisely the universal property, not a stronger hypothesis on the
  chosen maps. It concludes `IsIso p`, the same commutativity identity, and
  `q = p ≫ h ≫ j.inv` for that presentation.
- Unique comparison isomorphism commuting with both projections:
  `∃! c : F ≅ h.fiber ξ, c.hom ≫ h.fiberι ξ = p ∧
  c.hom ≫ h.fiberToSpecResidueField ξ = q`. Comparing each presentation to the
  fixed chosen fibre gives the unique projection-preserving comparison for any
  two choices by composing these isomorphisms. This states all the node's
  change-of-choice content.

Dependency declarations used and read:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme.Hom`, `AlgebraicGeometry.Spec`,
  `AlgebraicGeometry.Spec.map`, `AlgebraicGeometry.Scheme.ΓSpecIso`.
  This module also gives the proof dependency
  `AlgebraicGeometry.Scheme.ΓSpecIso_naturality` for
  lem-weil-pbc-spec-map-global-sections.
- `Mathlib.AlgebraicGeometry.ResidueField`:
  `AlgebraicGeometry.Scheme.residueField`, `.residue`, `.evaluation`,
  `.Γevaluation`, `.fromSpecResidueField`, and the recorded induced-map
  `.Hom.residueFieldMap`. The proof dependency
  lem-weil-pbc-spec-residue-field-identification is supplied by
  `AlgebraicGeometry.Scheme.Spec.residueFieldIso`,
  `.Spec.algebraMap_residueFieldIso_inv`, and
  `.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField` in this module.
- `Mathlib.AlgebraicGeometry.Fiber`: `AlgebraicGeometry.Scheme.Hom.fiber`,
  `.fiberι`, `.fiberToSpecResidueField`. Its pullback imports expose the general
  `CategoryTheory.IsPullback` interface for arbitrary presentations.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `.pullback.fst`, `.pullback.snd`, used through
  the preceding recorded fibre definitions and their universal property.
- Proof-only import `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`:
  `Ideal.ResidueField`, `Ideal.ker_algebraMap_residueField`,
  `Ideal.injective_algebraMap_quotient_residueField`, the quotient and zero-prime
  `IsFractionRing` instances, `Ideal.ResidueField.ringHom_ext`, and
  `Ideal.ResidueField.lift`, as recorded in
  lem-weil-pbc-prime-residue-field-algebra. All its clauses were read.

Edge cases checked mathematically: the empty W is included and its fibre is empty;
nonreduced and nonaffine W are included because invertibility is obtained from the
base isomorphism and the universal property. All characteristics, including two,
are allowed; the fraction calculation only uses the field axioms. ξ is not
required to be a particular syntactic presentation of the zero prime. Arbitrary
pullback choices are quantified over without assuming that their first projection
is invertible. A single explicit universe u is the usual category of u-small
schemes and fields; there is no extra smallness or equality assumption between
independent universes. Every variable is explicitly bound, and autoImplicit is
disabled. No statement dispute or node fault was found.

Searches performed for the full statement and its notions:

- `msearch.py leanfinder`, query "For a field K the canonical germ and residue map
  K to the residue field of Spec K is an isomorphism and every scheme over K is
  canonically its fibre at the unique base point": eight hits, including
  `Scheme.SpecToEquivOfField`, its equality criterion, the canonical residue-field
  over structures, and `fromSpecResidueField_apply`; none states this node.
- `msearch.py loogle`, query
  `AlgebraicGeometry.Scheme.fromSpecResidueField, CategoryTheory.IsIso`: zero hits.
- `msearch.py grep`, query
  `fromSpecResidueField.*[Ii]so|[Ii]so.*fromSpecResidueField|residueFieldIso`
  restricted to AlgebraicGeometry: seventeen ingredient hits in Fiber,
  AlgClosed/Basic, Morphisms/QuasiFinite, Morphisms/SmoothFiber and ResidueField.
  `residueFieldIsoBase` requires an algebraically closed base and finite-type
  hypotheses and does not give this statement. The prime-to-scheme residue-field
  comparison is already used from the recorded dependency.
- `msearch.py leansearch`, query "A scheme over a field is canonically isomorphic
  to its scheme theoretic fibre over the unique point of the spectrum of the
  field": eight hits, including `Scheme.Hom.fiber`, `Scheme.isoSpec`, the two fibre
  projections and `Scheme.SpecToEquivOfField`; none covers all the conclusions.
- `rg` in Mathlib, `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for `fieldBasePoint_fibre_isomorphism`,
  `fieldBasePoint`, `field_base_point`, and `FieldBasePointFibre`: no declaration
  name collision. The requested grep of the item id in `lean/WeilConjectures`
  has no hits.
- Conceptual `rg` in both project source trees for the canonical residue map,
  its invertibility and `residueFieldIso` finds ingredients and specialized
  arguments, including the private `localDim_asFiber_field` in
  `Sheaf.AlgebraicGeometry.AffineLimitFibreDimensionBoundCore`. Reading that lemma
  confirms that it only asserts local-dimension equality, not this node's field,
  global-section, projection and comparison conclusions. No duplicate was found.

Validation: scompile.py compiled this file separately against the published live
library in module mode, with no errors or warnings (sandbox 2.1 s, library 2.0 s).
All Lean source lines are at most 100 characters. Only the item's lean field is
added to the node copy; its reviewed split and natural-language statement stay
verbatim. No direct shared-repository edits or Git commands were run.

## Second reading by Q131

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
