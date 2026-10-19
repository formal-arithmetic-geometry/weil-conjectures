## Worker report

The single new module `Sheaf.Paper.FieldShriekLowerBound` states
`WeilConjectures.fieldShriek_lowerBound`, with its entire proof `by sorry`.
No definition is introduced. The theorem concerns the existing rationalized and
common finite-stage categories, the normalized compact-support morphism actions,
and their existing standard t-structures.

Hypothesis and clause correspondence:

- The global datum, including k as a fixed algebraic closure of a finite field,
  is `D : FiniteFieldDatum.{u}`. The coefficient prime is `l : ℕ`, `[Fact l.Prime]`,
  and `hl : l ≠ D.p`. The fixed coefficient closure is `Ω : Type v` with `[Field Ω]`,
  `[Algebra (Padic l) Ω]`, `[IsAlgClosure (Padic l) Ω]`.
- Each finite extension inside that closure is `E : Padic.FiniteCoefficientFields l Ω`.
  The existing `AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E` is its canonical
  small field model, algebra-isomorphic to the actual subfield of Ω. This is precisely
  the model used in the dependency's recorded `Stage`, not an extra field choice or
  a restriction on which finite extensions are covered. The scheme universe u and
  closure universe v remain independent.
- `X Y : Scheme.{u}`, their `.Over (Spec (.of D.k))` instances, and
  `[f.IsOver (Spec (.of D.k))]` mean a morphism of k-schemes.
  On each structure morphism `LocallyOfFiniteType` and `QuasiCompact` together mean
  finite type; `QuasiSeparated` is the node's quasi-separatedness hypothesis.
- `[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]` are exactly separated
  finite type for f. There is no separatedness binder on either structure morphism.
- `d : Compactification f` is universally quantified, as in the recorded construction
  of compact support. This is an arbitrary presentation of the operation, not a
  selected special compactification. Finite-type separated morphisms between these
  Noetherian qcqs schemes admit compactifications. The dependency's normalization
  identifies its functors with the proper/open construction for every such d.
- The rational category is `Stage l Ω X E`, definitionally the raw rationalization
  `sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X`. The finite functor is
  exactly `sfCompactSupportFiniteFunctor l D.k (PurCompactSupport.coefficientPrimeUnit
  l D hl) d (Coefficient.{u} l Ω E)`. Its map on every Hom is the existing scalar
  extension of the normalized integral action. No arbitrary action with the same
  object values is substituted.
- The common-stage category is `generalAlgebraicallyClosedConstructibleCategory l Ω X`.
  Its functor is `S.system.functor` for **every** `S : SfCompactSupportCoefficientAction
  l D.k (PurCompactSupport.coefficientPrimeUnit l D hl) Ω d`. This structure fixes
  all finite functors, literal output pairs and the normalized coefficient mates.
  The universal quantifier covers all presentations of this normalized operation;
  it does not assert the property of only a conveniently chosen action. Existence
  of normalized actions is the already landed `sfCompactSupportFiniteFieldIndependence`
  in `Sheaf.Paper.CompactSupportFiniteFieldIndependence`, used in the project wherever
  a concrete action is needed.
- At both levels the exactness conjunct is `∃ comm : F.CommShift ℤ, F.IsTriangulated`,
  with the second expression evaluated using that very instance by an explicit
  instance lambda. `CommShift ℤ` supplies coherent natural isomorphisms
  F(K[r]) ≅ F(K)[r] for every integer r, and `IsTriangulated` says the resulting
  triangle functor preserves distinguished triangles, including their connecting maps.
  These are conclusions, not assumed exactness hypotheses.
- Both lower-bound clauses quantify over every `c : ℤ`, every K in the corresponding
  category, and every `i : ℤ` with `i < c`. The antecedent and consequent are literally
  `IsZero ((constructibleTruncationCohomology t i).obj K)` and the same expression at
  `F.obj K`. The named cohomology functor is the dependency's
  `(t.truncLE i ⋙ t.truncGE i) ⋙ shiftFunctor _ i`, and t is respectively the recorded
  `sfRationalStandardTStructure` or `sfCommonStageStandardTStructure`. Those are the
  unique standard bounded t-structures with the prescribed classes; the structures
  of `constructibleTruncations_exists` have those same classes, hence agree.
  This renders exactly H^i(K)=0 for i<c implying H^i(Rf!K)=0 for i<c.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `def-weil-scheme-morphism-properties` is explicitly a convention node with no
  declaration: use Mathlib's `Scheme`, `Scheme.Over`, `Scheme.Hom.IsOver`,
  `LocallyOfFiniteType`, `QuasiCompact`, `QuasiSeparated`, `IsSeparated`.
- `Sheaf.Paper.QcqsCompactSupportRealization`:
  `WeilConjectures.sfQcqsCompactSupportRealization`, which reexports the integral,
  rational and Qbar values and the normalized finite action unchanged.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `generalAlgebraicallyClosedConstructibleCategory`,
  `GeneralAlgebraicallyClosedCoefficients.Stage`, `.Pair`, `.stageSystem`.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`,
  `sfRationalConstructibleShift`, `sfRationalConstructiblePretriangulated` and
  `sfRationalConstructibleTriangulated`; raw localization, no Karoubi envelope.
- `Sheaf.Paper.ConstructibleTruncations`: `constructibleTruncationCohomology`,
  `ConstructibleTruncations`, `constructibleTruncations_exists`.
- Mathlib `CategoryTheory.Triangulated.Pretriangulated` / `.Triangulated` / `.Functor`:
  `CategoryTheory.Pretriangulated`, `IsTriangulated`, `Functor.CommShift`,
  `Functor.IsTriangulated` (the recorded triangulated-category dependency match).
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, reexporting the existing coefficient
  integer rings, uniformizers and positive-level quotient rings. These data enter
  through the finite-action and coefficient-category definitions.
- Already landed `def-weil-compact-support-finite-action` is added to stmt_deps:
  module `Sheaf.Paper.CompactSupportFiniteAction`, declarations
  `WeilConjectures.sfCompactSupportFiniteFunctor` and
  `WeilConjectures.sfCompactSupportFiniteIntegralFunctor`.
- Already landed `def-weil-compact-support-coefficient-action` is added to stmt_deps:
  `Sheaf.Paper.CompactSupportCoefficientAction`, declaration
  `WeilConjectures.SfCompactSupportCoefficientAction`.
- Already landed `def-weil-constructible-heart` is added to stmt_deps:
  `Sheaf.Paper.SfConstructibleHeart`, declarations
  `WeilConjectures.sfRationalStandardTStructure` and `.sfCommonStageStandardTStructure`.
- `Sheaf.Paper.IntegralCompactSupportCoefficientComparison`:
  `WeilConjectures.PurCompactSupport.coefficientPrimeUnit`, used rather than adding
  a prime-invertibility assumption. All already recorded proof dependency modules
  are imported without `public`; statement imports are public.

Sources read: Bhatt--Scholze PDF, Definition 6.7.6, Lemma 6.7.7 and Lemma 6.1.13;
Stacks `more-etale.tex`, `lemma-derived-lower-shriek-bounded`, especially (3).
The latter preserves the left endpoint a and gives a finite upper cohomological
bound; the field passage and integral heart argument are the node's nine steps.
The full nine-step proof plan is in the theorem docstring, including the pro-zero
Tor tower, sheaf-valued Milnor sequence and bounded truncation induction.

Edge cases checked: K=0, empty source and empty target (the latter forces empty
source), E=Q_l (the bottom finite stage), arbitrary larger finite E, an independent
universe for Ω, all integer bounds including negative c, identity morphisms, open
immersions, proper morphisms, and nonseparated finite-type k-schemes with separated f.
For f=id the lower bound is sharp. For A^1 to a point compact support may create
higher cohomology but does not create cohomology below the bound. Shift convention
was checked against the dependency's explicit H^i formula; all integer shifts are
covered by `CommShift ℤ`.

Searches before writing (2026-10-18):

- `msearch.py ... leansearch "compact support pushforward is triangulated and preserves
  lower cohomological bounds"`: 8 hits, generic triangulated-functor constructors,
  exact-derived functors and t-structures, plus unrelated topological support; no match.
- `msearch.py ... leanfinder "compact support pushforward on constructible l-adic derived
  categories is triangulated and preserves lower cohomological bounds"`: 8 hits,
  generic derived t-structure and homological-kernel results; no adic compact-support match.
- `msearch.py ... loogle "CategoryTheory.Functor.IsTriangulated,
  CategoryTheory.Triangulated.TStructure.IsGE"`: 2 hits,
  `Functor.LeftTExact.mk` and `.isGE_obj`. These concern an abstract functor already
  known left t-exact; they do not establish this operation's lower bound.
- `msearch.py ... grep "compactSupport|CompactSupport|shriek|Shriek" CategoryTheory`:
  zero hits in Mathlib's category-theory files.
- `rg` in upstream `WeilConjectures` for the item id, finite functor, Qbar compact
  support and proposed theorem names; `grep -rn` for the exact item id: no match.
- `rg` in project `lean/Sheaf/Paper/*CompactSupport*.lean` and relevant modules found
  the existing normalized finite action, coefficient action, object values and
  qcqs realization, all reused. No theorem already states the present exactness
  and lower-bound conjunction. The consumer `CompactSupportLerayFiltration` cites
  this pending item in its proof docstring, not as an existing declaration.
- Proposed declaration name checked in `dag/lean_names_upstream.json`, upstream
  `WeilConjectures` and `lean/Sheaf`: no collision.

No statement correction, disputed assertion, new node or dependency repair is needed.
Only the lean record and the three added landed statement dependencies change.

## Second reading by NO

Author's separate rereading, with the JSON and full Lean module open; the maintainer's
independent review remains the independent mathematical check. I matched the finite-field
and coefficient binders, all six structure-morphism property binders, the morphism-over-base
binder and separated finite-type f, and verified that no structure-morphism separatedness
was inferred as an extra assumption. I checked the two coefficient cases separately:
finite stages use the literal recorded small field model, and the Qbar case quantifies
universally over normalized actions. For each, exactness uses the same existential shift
instance in `IsTriangulated`; the lower-bound implication quantifies over all integers
and all objects and tests literal truncation cohomology. Both input and output use the
same coefficient field or closure and the standard t-structures on X and Y respectively.
The normalized action includes morphisms and coefficient mates, so objectwise values
have not been substituted for the functor. No private definitions, local notation,
auto-bound universes, let binders, or proved theorems occur. No mismatch was found.
The additional stmt_deps name existing landed notions explicitly used by the signature.

Validation is recorded below after compilation and delivery preflight.

Validation: prescribed `scompile.py NO lem-zl-field-shriek-lower-bound` succeeded
on 2026-10-18 for the complete file, with no errors or warnings. Both the wrapper's
sandbox check and its final library-path confirmation were clean (the latter 6.4 s).
The JSON delta was checked to contain only `lean` and the three added landed
`stmt_deps`; there is one theorem and its whole proof is `sorry`.

The prescribed `deliver2.py NO lem-zl-field-shriek-lower-bound --no-push`
reported `OK (dry run)` on 2026-10-18: preflight and compilation both passed.
