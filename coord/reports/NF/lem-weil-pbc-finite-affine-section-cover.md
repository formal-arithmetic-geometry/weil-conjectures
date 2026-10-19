## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteAffineSectionCover` states
`AlgebraicGeometry.exists_finite_affine_section_cover`, with `sorry` as its entire proof.
The statement matches Stacks Morphisms, Tag 03HW, lemma-massage-finite, clauses (1)–(5),
read in literature/stacks-project/morphisms.tex. No statement correction or new notion is needed.

Clause-by-clause correspondence:

- Schemes and the finite morphism: `{X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f]`.
- Affine base: `[IsAffine X]`; there is no Noetherian, reducedness, nonemptiness or field hypothesis.
- Affine base change: `∃ (X' : Scheme.{u}) (a : X' ⟶ X), IsAffine X' ∧
  Surjective a ∧ a.IsFiniteLocallyFree ∧ ...`.
- Affine ambient scheme and finite locally free structure morphism:
  `∃ (W : Scheme.{u}) (p : W ⟶ X') ... , IsAffine W ∧ p.IsFiniteLocallyFree ∧ ...`.
- The actual fibre product is `pullback f a`, whose projections are `pullback.fst f a` to
  `Y` and `pullback.snd f a` to `X'`. Thus `j : pullback f a ⟶ W`,
  `IsClosedImmersion j`, and `j ≫ p = pullback.snd f a` express the closed immersion over `X'`.
- A finite family of closed subschemes is encoded by `n : ℕ`, `Z : Fin n → Scheme.{u}`,
  `i : ∀ k : Fin n, Z k ⟶ W` with `∀ k, IsClosedImmersion (i k)`.
  A scheme equipped with a closed immersion is precisely a representative of a closed subscheme;
  no extra choice of ideal sheaf or duplicated definition is needed.
- Each restriction is an isomorphism: `∀ k, IsIso (i k ≫ p)`.
- Set-theoretic coverage: `∀ w : W, ∃ (k : Fin n) (z : Z k), i k z = w`.
- The final projection is surjective finite locally free:
  `Surjective (pullback.fst f a) ∧ (pullback.fst f a).IsFiniteLocallyFree`.

Dependency declarations, with their signatures and docstrings inspected:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
  Affineness is Mathlib's `AlgebraicGeometry.IsAffine` in AffineScheme (canonical map to
  the spectrum of global sections is an isomorphism).
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `AlgebraicGeometry.Surjective`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree`, extending finite, flat, locally of
  finite presentation exactly as the dependency node states.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`; existence for schemes comes from
  `Mathlib.AlgebraicGeometry.Pullbacks`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion` (closed embedding with surjective stalk maps).

The module also imports stated proof dependencies: finite-algebra integrality from
`Mathlib.RingTheory.IntegralClosure.Algebra.Basic`; monic splitting and monic quotient bases
from `Mathlib.RingTheory.AdjoinRoot`; integral lying over from
`Mathlib.RingTheory.Spectrum.Prime.Topology`; base-change bases from
`Mathlib.LinearAlgebra.TensorProduct.Basis`. The finite-free algebra spectrum node has no
recorded statement module yet, so no import can be added for it. The affine spectrum,
closed immersion criterion, affine tensor-product pullback, free-module and tensor-product
notions are supplied by the other imports. The complete seven-step node proof is included
in the theorem docstring; no step is proved in this delivery.

Edge cases checked: empty `X` forces empty `Y`, and identity maps with a one-member cover
work; empty `Y` over a nonempty base is allowed; `n = 0` for the cover is allowed and forces
`W` empty through the pointwise coverage clause. The algebra construction with no generators
uses a singleton empty tuple, not an empty cover. Repeated roots and nonreduced rings cause
no problem because coverage is set theoretic. All schemes use the same arbitrary universe
`u`, including the witnesses; finite indices use `Fin n`. No auto-bound variables occur.

Searches for an existing statement (2026-10-15):

- `msearch.py ... leanfinder`: “A finite morphism of affine schemes embeds after finite
  locally free surjective base change into a finite locally free scheme covered by closed
  sections”. Eight results about `IsFinite`, affineness and finite type, none the cover theorem.
- `msearch.py ... loogle`: `AlgebraicGeometry.IsFinite, AlgebraicGeometry.IsClosedImmersion`.
  Three results: closed immersions are finite, and finite mono iff closed immersion;
  none supplies the ambient section cover.
- `msearch.py ... grep`: `massage|section.*finite.*free|finite.*free.*section`.
  Eleven unrelated results, none the theorem.
- `msearch.py ... leansearch`: “A finite affine morphism admits a finite section covered
  ambient scheme”. Service unavailable (Internal Server Error).
- `rg` in upstream `WeilConjectures` and project `lean/Sheaf` for `massage`,
  `finite_affine_section_cover`, `finiteAffineSectionCover`, and the exact node id: no match.
  The selected declaration name is absent from Mathlib and both project source trees.
- Upstream name inventory search `finite.*section.*cover|section.*cover.*finite` only found
  `Scheme.Modules.exists_finite_generatingSections_tensorPow_of_affine_section_cover`,
  a statement about generating sections of module tensor powers, not this scheme cover.

Validation: server-only scompile.py compiled the initial module cleanly in 1.4 seconds,
with nice 19, two threads and the 60-second per-file limit. Final imports and metadata are
checked again by the required deliver2.py dry run. No local compiler or library build used.

## Second reading by NF

Independent reading against the node and Stacks morphisms.tex, label
lemma-massage-finite (Tag 03HW), including the surrounding finite-locally-free
section. The source assumes only a finite morphism and an affine target.
Its lemma-finite-flat identifies finite local freeness with finite, flat,
and locally of finite presentation without a Noetherian hypothesis.

Objects, hypotheses, and conclusion clauses, checked individually:

1. Schemes X and Y and their morphism f: `{X Y : Scheme.{u}} (f : Y ⟶ X)`.
   Verdict: exact; X is the target, Y the source, with arbitrary universe u.
2. Finiteness of f: `[IsFinite f]`. Verdict: exact. Opened the recorded
   Mathlib Morphisms.Finite declaration: it extends IsAffineHom and requires
   finite ring maps on every affine open of the target.
3. Affineness of X: `[IsAffine X]`. Verdict: exact. Opened AffineScheme:
   this means the canonical map to Spec of global sections is an isomorphism.
   Opened Scheme: schemes are locally ringed spaces locally isomorphic to spectra.
   No extra instance, field, separatedness, Noetherian or nonzero assumption occurs.
4. Affine X' and a surjective finite locally free map to X:
   `∃ (X' : Scheme.{u}) (a : X' ⟶ X), IsAffine X' ∧ Surjective a ∧
   a.IsFiniteLocallyFree ∧ ...`. Verdict: exact. Opened UnderlyingMap:
   Surjective is surjectivity on points. Opened the recorded upstream
   FiberDegree declaration: IsFiniteLocallyFree extends IsFinite, Flat and
   LocallyOfFinitePresentation, exactly the dependency node's definition and
   the source's equivalent criterion. The surrounding section adds no hypotheses.
5. The base-changed Y': `pullback f a`. Verdict: exact. Opened HasPullback:
   this is the limit of the cospan, fst maps to Y and snd to X'. Opened
   AlgebraicGeometry.Pullbacks: HasPullback is supplied for arbitrary scheme
   morphisms. The order Y times_X X' rather than X' times_X Y is immaterial,
   with the projections correctly assigned. No separate arbitrary Y' is used.
6. Affine W and finite locally free p to X': existential `W`, `p`, with
   `IsAffine W ∧ p.IsFiniteLocallyFree`. Verdict: exact. Both affineness clauses
   are in the node; in the source they follow from finite morphisms over affine X.
7. Closed immersion of Y' into W over X': `j : pullback f a ⟶ W`,
   `IsClosedImmersion j`, and `j ≫ p = pullback.snd f a`. Verdict: exact;
   the equality expresses the required triangle, not merely an unrelated immersion.
   Opened Morphisms.ClosedImmersion: closed embedding and surjective stalk maps,
   equivalent to the dependency node's sheaf-surjection definition.
8. Finite family of closed subschemes: `∃ (n : ℕ) (Z : Fin n → Scheme.{u})
   (i : ∀ k : Fin n, Z k ⟶ W), (∀ k, IsClosedImmersion (i k) ∧ ...)`.
   Verdict: exact. A scheme with a closed immersion represents a closed subscheme;
   finite indexing by Fin n loses no finite family and imposes no distinctness.
9. Each restriction maps isomorphically to X': `IsIso (i k ≫ p)` for every k.
   Verdict: exact; it is the restriction of the same p, not some chosen isomorphism.
10. Set-theoretic coverage of W: `∀ w : W, ∃ (k : Fin n) (z : Z k), i k z = w`.
    Verdict: exact union of the images, with no scheme-theoretic union or
    disjointness requirement. The family is chosen before its pointwise witnesses.
11. Projection Y' to Y surjective finite locally free:
    `Surjective (pullback.fst f a) ∧ (pullback.fst f a).IsFiniteLocallyFree`.
    Verdict: exact; these properties belong to the first projection, not to f or j.

Edge cases: empty X and hence empty Y are admitted; identities and a single
closed member give the claimed diagram. Empty Y over nonempty X is admitted
(the empty closed subscheme can immerse into the ambient W). Fin n permits
n = 0, when coverage forces W empty, exactly as an empty union does. In the
construction the zero-generator case instead has one empty tuple and W = X'.
Zero rings, arbitrary characteristic, nilpotents and repeated roots are not
excluded. All schemes and witnesses lie in arbitrary Scheme.{u}; finite ring
extensions, quotients and fibre products stay in that universe. No universe
or variable is unbound, and no independent too-small test universe occurs.

Independent searches used different phrasing from the worker:

- msearch leanfinder: “Finite morphism to an affine scheme has a finite faithfully
  flat base change admitting a closed embedding into a scheme covered set
  theoretically by closed sections”. Eight hits, including isFinite_iff,
  finite_appTop_of_universallyClosed and IsFinite; none states this theorem.
- msearch loogle: `AlgebraicGeometry.IsFinite, AlgebraicGeometry.Surjective,
  AlgebraicGeometry.IsClosedImmersion`. Zero hits.
- msearch grep in Mathlib AlgebraicGeometry: `closed.*section|section.*closed|massage`.
  Seven unrelated hits (section headings, zero loci, stalks, ideal sheaves).
- Direct rg in upstream WeilConjectures, project lean/Sheaf, and the upstream
  name inventory for `03HW|massage|finite_affine_section_cover|finiteAffineSectionCover|
  covered by.*sections|union of closed subschemes` found no equivalent statement.
  Broader closed-section/section-cover searches found unrelated statements;
  opened exists_finite_generatingSections_tensorPow_of_affine_section_cover:
  it concerns generators of twisted modules on an open cover, not this diagram.
  The worker's LeanSearch service-unavailable result remains recorded as such.

There are no new nodes, dependency modules, corrected statements or citer
verdicts to review. The six statement dependency nodes and their recorded
signatures were read, and their actual source declarations opened as above.
The existing proof-dependency modules are imported; the finite-free-algebra
spectrum lemma has no statement module yet, as the worker reported.
The theorem docstring follows all seven proof steps, including empty cases,
splitting, injectivity/lying over, monic quotient bases, the closed immersion,
closed root sections and the final base-changed basis. No definitions or
proofs were added: the only theorem has `sorry` as its whole proof. Source and
blueprint docstrings, namespace, imports and line lengths meet the conventions.

No mismatch found. Changed only this report by adding the independent reading;
the Lean module and node signature remain unchanged. The node's lean.statement
was checked verbatim against the theorem signature. Validation uses scompile.py
on the server only, followed by deliver2.py dry run and delivery.
