## Worker report

The delivery states the node as two theorems in
`Sheaf.AlgebraicGeometry.RationalSmoothLimitModels`:
`AlgebraicGeometry.exists_rational_smooth_limit_models` and
`AlgebraicGeometry.regular_hom_descends_to_smooth_stage`. Both proofs are `sorry`.
The first docstring records all twelve proof steps, with the dependency ids; the
second gives the comparison argument from steps 5–6 and 8–12. No statement is
corrected. The only new notion is the genuine predicate of generic reducedness.

Clause-by-clause rendering of the existence assertion:

- “X affine”: `(X : Scheme.{u}) [IsAffine X]`.
- “finite disjoint union”: `(A : Type u) [Finite A]`, schemes `C a`, coprojections
  `ι`, and `hc : IsColimit (Cofan.mk X ι)`. A coproduct cocone in schemes is precisely
  the disjoint union, including the empty coproduct. No connectedness is imposed
  on its summands. Affineness of the summands follows from affineness of X.
- “finite type over characteristic-zero fields, fields may differ”: the dependent
  family `K : A → Type u`, `[∀ a, Field (K a)]`, `[∀ a, CharZero (K a)]`, structure
  morphisms `s a : C a ⟶ Spec (CommRingCat.of (K a))`, and
  `hft : ∀ a, LocallyOfFiniteType (s a) ∧ QuasiCompact (s a)`.
- “generically reduced”: `hred : ∀ a, IsGenericallyReduced (C a)`.
  The definition tests `_root_.IsReduced (X.presheaf.stalk x)` for exactly the
  points `x ∈ genericPoints X`. It does not replace this by globally reduced.
- “small nonempty directed set”: existential `I : Type u` with `Preorder I`,
  `IsDirected I (· ≤ ·)` and `Nonempty I`. This is the project's directed-set
  convention; the index universe equals the scheme universe.
- “inverse system”: `D : Iᵒᵖ ⥤ Scheme.{u}`; a natural transformation
  `p : (Functor.const Iᵒᵖ).obj X ⟶ D` supplies the compatible projections.
- “limit in schemes is X”: `Nonempty (IsLimit (Cone.mk X p))`, in Scheme itself.
- “affine generically reduced finite-type rational stages”: for every `i`,
  `IsAffine (D.obj i) ∧ IsGenericallyReduced (D.obj i)` and an existential
  `t : D.obj i ⟶ Spec (CommRingCat.of (ULift.{u} ℚ))` with
  `LocallyOfFiniteType t ∧ QuasiCompact t`. The universe lift represents the same
  rational field in the scheme universe; it places no algebraic restriction.
  A rational structure morphism, when it exists, is unique; thus the diagram's
  scheme morphisms already respect rational coefficients.
- “smooth affine transition morphisms”: for all arrows of the opposite preorder,
  `Smooth (D.map f) ∧ IsAffineHom (D.map f)`.
- “regular projections”: `IsRegularSchemeMorphism (p.app i)`.
- “one may choose schematically dominant”: the same chosen system satisfies
  `IsSchemeTheoreticallyDominant (p.app i)` for every i. Taking this optional
  choice together with the other properties is exactly the asserted existence.
- “empty schemes allowed and finite unions”: neither A nor the schemes have a
  Nonempty binder. Only the approximation index I is nonempty.

Clause-by-clause rendering of the comparison assertion:

- “ANY two systems”: arbitrary directed nonempty `I,J : Type u`, arbitrary
  functors `D,E`; `hD,hE` assert affine finite-type rational stages. Unlike the
  existence theorem, there is no generic-reducedness hypothesis here.
- “smooth affine transitions”: `hDt,hEt`, for all arrows of the respective diagrams.
- “Noetherian limits X,Y”: cones `c,d`, witnesses `hc : IsLimit c`,
  `hd : IsLimit d`, and `[IsNoetherian c.pt] [IsNoetherian d.pt]`. This uses
  arbitrary cone vertices, not a chosen limit object or an arbitrary comparison.
- “h regular”: `(h : d.pt ⟶ c.pt) (hh : IsRegularSchemeMorphism h)`.
- “for every i and every j₀”: final unrestricted binders `(i : I) (j₀ : J)`.
- “some j ≥ j₀ and SMOOTH hji”: `∃ j, j₀ ≤ j ∧ ∃ hji, Smooth hji ∧ ...`, with
  `hji : E.obj (op j) ⟶ D.obj (op i)`. Smoothness is global at the finite stage.
- “p_i h = hji q_j”: `h ≫ c.π.app (op i) = d.π.app (op j) ≫ hji`.
- “identity with two presentations”: substitute equal cone vertices and `h = 𝟙 X`;
  identities are regular. Nothing identifies the two diagrams or their indices.
- “no compatibility of ground fields”: no ground fields or compatibility data
  occur in the comparison theorem; only the unique rational structure exists.
- “finite-stage scheme morphisms, not desingularization towers”: the conclusion
  is an actual `Scheme.Hom` with `Smooth`; no tower or resolution occurs.

Recorded dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`; and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`:
  `AlgebraicGeometry.QuasiCompact`. Their conjunction is exactly finite type,
  as the existing dependency record specifies.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`, whose
  documented equivalent stalkwise form supplies reducedness of the generic
  stalks; the new predicate uses the existing root ring `IsReduced`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
  The relative-dimension and etale declarations of that dependency are not used
  by this node's statement.
- `Sheaf.AlgebraicGeometry.RegularSchemeMorphism`:
  `AlgebraicGeometry.IsRegularSchemeMorphism`, read in full. It is `Flat f` and
  regularity of the scheme-theoretic fibre after every finite residue-field
  extension, with the test field in Type u. No private regularity predicate.
- New generic-reducedness node: `Sheaf.AlgebraicGeometry.GenericallyReducedScheme`,
  `AlgebraicGeometry.IsGenericallyReduced`, on top of the recorded generic-point,
  scheme and reduced-scheme notions. `Mathlib.Topology.Sober.genericPoints` is
  exactly the points whose singleton closure is an irreducible component.
- Schematic dominance reuses
  `Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant`:
  `AlgebraicGeometry.IsSchemeTheoreticallyDominant`, defined by `f.ker = ⊥`.
  No second definition is made.
- All recorded modules of stated proof dependencies are plain imports. The
  currently unstated `lem-per-flat-model-generic-reducedness` is proof-only, so
  it introduces no missing statement notion and has no module to import.

Edge cases checked: empty A and empty X; singleton index and constant systems;
empty stages and empty limits in the comparison; disconnected finite unions
with distinct ground fields; characteristic-zero fields of arbitrary
transcendence degree; singular but generically reduced stages; embedded
nilpotents (for example k[x,e]/(e²,xe), generically reduced but not reduced);
identity between unrelated presentations; arbitrary prescribed j₀; systems
with nonsurjective projections or noninjective transition ring maps. The
statement retains all these cases and adds no surjectivity, reducedness or
field-linearity assumption. The zero scheme has no generic points, so the
new predicate is vacuously true, as required. The proof's bad-locus argument
handles an empty limit without assuming surjectivity of a projection.

Searches before writing (all msearch commands used group Q27 and this item):

- LeanFinder: “An affine generically reduced variety over a characteristic zero
  field is an inverse limit of affine finite type rational schemes with smooth
  transition maps and regular maps descend to smooth finite stage maps”:
  eight hits, including IsSmooth, IsAffine, IsReduced, IsIntegral and pointwise
  smoothness. None gives the node's theorem.
- Loogle: “AlgebraicGeometry.Smooth, CategoryTheory.Limits.IsLimit”: 0 hits.
- msearch grep: “generically.?reduced|smooth.*[Ll]imit|[Ll]imit.*smooth” in
  AlgebraicGeometry: 0 hits.
- rg on WeilConjectures and Sheaf for generic reducedness and rational smooth
  model names: no existing theorem or generic-reducedness predicate. Existing
  smooth-colimit regularity and affine-limit modules give proof inputs only.
- rg for this item's blueprint id in WeilConjectures: no match.
- The three further searches for the new predicate, plus DAG and blueprint
  searches, are recorded verbatim in its `mathlib_searches` summaries below.

Source verification: read arXiv:0905.3580v1 directly at
https://arxiv.org/pdf/0905.3580, especially Definition 7.2, the proof of Theorem
7.4 (fix i, factor through Yj, pass to the smooth locus, factor again at k), and
Theorem 7.5 with its schematic-image refinement. The new predicate merely names
the explicit generic-reducedness condition already present in the DAG node;
it does not claim the paper states a new definition with this exact name.
No mathematical fault or STATEMENT-DISPUTED flag remains.

Validation: both delivered modules compiled separately in dependency order via
`scompile.py Q27 lem-per-variety-rational-smooth-limit-models ...`, including
sandbox and library modes, with no errors or unexpected warnings. No lake build
or direct repository mutation was used.

## New nodes

`def-per-generically-reduced-scheme` defines reducedness of the local ring at
every generic point of an irreducible component. It cites the existing scheme,
generic-point and reduced-scheme definition nodes and has real Prop data with
no sorry. Its source is the explicit generic-reducedness specialization of
BMT §7 in the item's statement/proof step 3. LeanSearch found reducedness at
all stalks and `genericPoints`; LeanFinder found only globally reduced notions;
Mathlib grep, project grep, blueprint search and the definition-node scan
found no predicate imposing only generic reducedness. Thus this names a missing
notion rather than copying a reduced-scheme definition. It is cited by the item.

## Second reading by Q27

The dispatcher explicitly prohibits starting another agent. This section is a
second pass by the same worker; the maintainer's independent review remains
independent and is not represented as already performed here.

I reopened the node, both final signatures and the new definition. The existence
hypotheses match exactly via a finite coproduct cocone; I changed the initially
written `Fin n` component family to an arbitrary `A : Type u` with `[Finite A]`
to follow the project's finite-index convention and preserve empty families.
Both the stage schemes and arbitrary test fields use the scheme universe.
The generic-reducedness predicate tests only `genericPoints`, not all stalks.
The rational base uses ULift ℚ and is not an additional field choice. The
existence result includes dominance and regularity on the very same projections
that form the limit cone. In the second theorem I specifically checked that
there is no generic-reducedness or dominance assumption, that j₀ is unrestricted,
that the finite-stage map is smooth rather than merely regular, and that the
composition equality is oriented correctly in Lean's left-to-right notation.
No hypothesis or clause is omitted; no source-based correction is needed.
