## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleCompactSupportOpenClosedTriangle` states
`AlgebraicGeometry.Etale.exists_compactSupport_openClosed_triangle`, with proof `sorry`.
There are no new definitions, dependency replacements, or statement corrections.

Hypothesis and conclusion correspondence:

- The finite commutative coefficient ring is `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
  This is the six-functor encoding of module sheaves specified by the derived-categories
  dependency, with no nonzero-ring or invertibility restriction.
- The schemes are `{U Z X Y : Scheme.{u}}`. Quasi-compactness and quasi-separatedness
  of X and Y are `[CompactSpace X] [QuasiSeparatedSpace X]` and their Y analogues.
- The separated finite-type map is `(f : X ⟶ Y) [IsSeparated f]
  [LocallyOfFiniteType f] [QuasiCompact f]`. Finite type means locally finite type
  and quasi-compact, as fixed by the conventions node.
- The quasi-compact open immersion is `(j : U ⟶ X) [IsOpenImmersion j]
  [QuasiCompact j]`. The closed immersion is `(i : Z ⟶ X) [IsClosedImmersion i]`.
  `hij : Set.range i.base = (Set.range j.base)ᶜ` states exactly the complement condition.
  No reducedness or finite presentation of the closed ideal is imposed.
- The bounded-below input is
  `K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))`.
- The restrictions g and h are written `j ≫ f` and `i ≫ f`. Their independent chosen
  compactifications are `c_g : Compactification (j ≫ f)` and
  `c_h : Compactification (i ≫ f)`, alongside `c_f : Compactification f`.
  `Compactification` supplies an open immersion, proper second map, and factorization.
  Although its general definition permits non-quasi-compact open factors, here those
  factors are automatically quasi-compact: f and both restrictions are quasi-compact,
  and `Compactification.quasiCompact_openImmersion_iff` applies. Thus no compactification
  permitted by these binders is outside the node's specified compactifications.
- The existential `T : Triangle (DerivedCategory (Sheaf Y.smallEtaleTopology
  (ModuleCat.{u + 1} Λ)))` and `T ∈ distTriang _` state existence and distinguishedness.
  The three `Nonempty (T.objᵢ ≅ ...)` identify its vertices respectively with
  `Rg_!^{c_g} j⁻¹ K`, `Rf_!^{c_f} K`, and `Rh_!^{c_h} i⁻¹ K`.
  Inverse images use the existing exact `upperStar` via `mapDerivedCategoryPlus`;
  pushforwards use `rightDerivedLowerShriekOfCompactificationPlus`, exactly `Rp_* j_!`.
  The last `.obj` forgets the bounded-below predicate. The triangle is expressed in
  the ambient derived category, as in Tag 0GKP. All vertices are isomorphic to objects
  of the strictly full triangulated D⁺, so this is equivalently the triangle in D⁺.
  Transport along these vertex isomorphisms gives arrows on the displayed terms.
- For every `q : ℤ`, `z₂`, `z₃`, `z₁` certify the consecutive composites are zero,
  and the three `ShortComplex.mk ... .Exact` conjuncts assert exactness respectively at
  H^q(T.obj₂), H^q(T.obj₃), and H^(q+1)(T.obj₁). As q ranges over all integers,
  this is the entire displayed long exact sequence. Its connecting map is the existing
  `DerivedCategory.HomologySequence.δ T q (q + 1)`, induced by the third triangle arrow
  and the cohomology-shift isomorphism, not an unrelated existential connecting map.
  `DerivedCategory.homologyFunctor` gives exactly the specified cohomology sheaves.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- The convention record has no declaration; its properties are Mathlib classes above.
- `WeilConjectures.Compactification.Defs`: `AlgebraicGeometry.Compactification`, including
  its docstring on quasi-compact open factors.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification` and its bounded-below
  counterpart `rightDerivedLowerShriekOfCompactificationPlus`; the latter is used here.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `AlgebraicGeometry.Etale.openImmersionLowerShriek`, used by that compact-support functor.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.upperStar`, `lowerStar`, `upperStarLowerStarAdjunction`.
  Upper star occurs directly and lower star inside the compact-support definition.
  The source's derived direct image is the generic `rightDerivedFunctorPlus` applied
  to lower star, as documented in `SixFunctors.Etale.Derived.UpperLowerStar`.
- `Sheaf.AlgebraicGeometry.DerivedCategories`: the mixed dependency record documents
  D⁺ of exactly these module-valued sheaves. Its source declarations
  `DerivedCategory`, `DerivedCategory.Plus` are used rather than copied.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory` and its triangulation.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor` and `DerivedCategory.HomologySequence.δ`.
  This is the generic cohomology-sheaf dependency specialized to module-valued sheaves,
  consistently with the derived-categories dependency and its six-functor encoding.

Imports also include the recorded available proof modules: QuasiSeparated,
ZariskisMainTheorem, FinitePresentation, EtaleModuleEnoughInjectives,
EtaleConstantModuleDirectImageLeftExact, EtaleModuleSheavesGrothendieckAbelian.
Exact functor and right-derived triangulation dependencies are imported transitively
by Derived.LowerShriek; the long exact sequence and triangulation dependencies by
DerivedCategories. The proof dependencies `lem-cbc-open-closed-recollement` and
`lem-weil-pbc-etale-shriek-qcqs-composition` have no recorded module on this base, so no
import can yet be added for those nodes. They remain named in the proof docstring.

Edge cases checked: U empty (the closed term is all of X); U all of X (the closed
term is zero); X empty; zero K; the zero coefficient ring; negative and zero q;
nonreduced closed complements and non-finitely-presented closed ideals. The statement
imposes none of the exclusions that would lose these cases. Finite rings are torsion,
so Tag 0GKP's torsion condition is automatic. No properness of f, finite cohomological
dimension, or compatibility of the three chosen compactifications is assumed.

Searches (2026-10-15; full tool results are in sandbox `searches.jsonl`):

- `msearch.py ... leanfinder "Relative etale compact support open closed localization
  distinguished triangle"`: eight hits on the etale locus and qcqs sections, none on
  the requested triangle.
- `msearch.py ... loogle '"shriek"'`: zero hits.
- `msearch.py ... grep 'compactSupport.*triangle|openClosed|open_closed' CategoryTheory`:
  zero hits.
- `msearch.py ... leansearch "Etale compactly supported derived pushforward localization
  triangle"`: unavailable, Internal Server Error; no inference from this unavailable search.
- `rg -n 'openClosed|open_closed|compactSupport.*triangle|<item id>'` in the upstream
  WeilConjectures and this project's lean/Sheaf: absolute open-closed triangles
  (`exists_distTriang_openClosed`), short exact sheaf sequences, and specialized Weil
  weight statements. Read the absolute triangle's full signature and docstring; it
  does not give the relative, independently compactified statement. No occurrence of
  the item's own blueprint id upstream. Searched Derived/LowerShriek* for triangle:
  compactification-composition data only, no relative localization triangle.

Source read: `literature/stacks-project/more-etale.tex`, label
`lemma-relative-triangle-associated-to-open`, statement and proof. The node is its
finite-commutative-ring bounded-below specialization, with the cohomological consequence
spelled out. No statement fault or STATEMENT-DISPUTED issue found.

Validation: server-only `scompile.py` passed without errors or warnings; the delivered
file took 1.9 seconds, nice 19, two threads, 60-second per-file limit. The server also
compiled the side dependency EtaleConstantModuleDirectImageLeftExact in its private
overlay. No local compiler or library build was run.

## Second reading by NZ

Independently read the sandbox node, its source in `more-etale.tex`, label
`lemma-relative-triangle-associated-to-open` (Tag 0GKP), the Lean module, all ten
statement-dependency records, and the definitions used below. There is no
`statement_change`, new definition node, or dependency module in this delivery.
The node is the finite-commutative-ring, bounded-below specialization of the
source; the source's torsion requirement is automatic for these coefficients.

Object, hypothesis, and conclusion checklist, in node order:

1. Finite commutative coefficient ring: `(Λ : Type (u + 1)) [CommRing Λ]
   [Finite Λ]`. PASS. No field, nontriviality, characteristic, invertibility,
   constructibility, or Noetherian hypothesis is inserted.
2. Schemes and small-etale module derived categories: `{U Z X Y : Scheme.{u}}`
   and `Sheaf _.smallEtaleTopology (ModuleCat.{u + 1} Λ)`, with
   `DerivedCategory.Plus` for the input and all three functor outputs. PASS.
   Read `Scheme`, `DerivedCategory`, `DerivedCategory.Plus` (the standard
   t-structure's full subcategory), and the mixed record/module
   `Sheaf.AlgebraicGeometry.DerivedCategories`: this is exactly its recorded
   six-functor encoding, rather than a new module-sheaf notion.
3. X and Y quasi-compact and quasi-separated: `[CompactSpace X]`,
   `[QuasiSeparatedSpace X]`, and the two Y analogues. PASS. The node does not
   require additional explicit hypotheses on U and Z: the quasi-compact open
   immersion and the closed immersion into qcqs X imply their qcqs properties.
4. Separated finite-type map: `(f : X ⟶ Y) [IsSeparated f]
   [LocallyOfFiniteType f] [QuasiCompact f]`. PASS. Read Mathlib's class
   signatures; locally finite type plus quasi-compact is the convention node's
   finite type, with no finite-presentation condition.
5. Quasi-compact open and closed complement: `(j : U ⟶ X) [IsOpenImmersion j]
   [QuasiCompact j]`, `(i : Z ⟶ X) [IsClosedImmersion i]`, and
   `hij : Set.range i.base = (Set.range j.base)ᶜ`. PASS. Read
   `IsClosedImmersion`; equality of underlying images specifies a closed
   complement without requiring its scheme structure to be reduced.
6. Restrictions of f: `j ≫ f` and `i ≫ f`. PASS; Lean composition order is
   the node's g = f j and h = f i.
7. Every bounded-below K: the explicit binder
   `K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))`.
   PASS. There is no uniform bound or bound on cohomological dimension.
8. Every three chosen compactifications: `c_f : Compactification f`,
   `c_g : Compactification (j ≫ f)`, `c_h : Compactification (i ≫ f)`.
   PASS. Read `Compactification` in `WeilConjectures.Compactification.Defs`:
   it supplies the proper map, open immersion, and factorization. Its open
   immersion is automatically quasi-compact in this context by
   `Compactification.quasiCompact_openImmersion_iff`, since f, j ≫ f, and
   i ≫ f are quasi-compact. The latter follows from closed immersions being
   quasi-compact; no extra compatibility between compactifications is assumed.
9. Compact support means Rp_* j_!: read
   `rightDerivedLowerShriekOfCompactificationPlus`, whose body is exact
   extension by zero followed by bounded-below right derived direct image.
   Also read `openImmersionLowerShriek`, `lowerStar`, `upperStar`, and
   `upperStarLowerStarAdjunction` in their recorded dependency modules.
   PASS. The `.mapDerivedCategoryPlus` applied to `upperStar` is inverse
   image on complexes, not exceptional inverse image or O-module pullback.
10. Distinguished triangle with the three required terms: `∃ T : Triangle
    (DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))`,
    the ordered three `Nonempty (T.objᵢ ≅ ...)` clauses, and
    `T ∈ distTriang _`. PASS. These terms are respectively the c_g pushforward
    of j-inverse-image K, the c_f pushforward of K, and the c_h pushforward
    of i-inverse-image K. The final `.obj` includes D-plus in D. Transporting
    the triangle along the vertex isomorphisms gives precisely the displayed
    triangle on those terms. D-plus is strictly full and triangulated; thus
    the ambient-category encoding neither loses nor adds a case.
11. Entire cohomology-sheaf exact sequence: `∀ q : ℤ`, the witnesses
    `z₂`, `z₃`, `z₁` and the three `ShortComplex.mk ... .Exact` clauses.
    PASS. They assert exactness at H^q of the middle term, H^q of the closed
    term, and H^(q+1) of the open term. Every position occurs as q varies.
    Read `DerivedCategory.homologyFunctor`, `HomologySequence.δ`, and
    `exact₂`, `exact₃`, `exact₁` in Mathlib's `HomologySequence.lean`:
    δ uses T.mor₃ and the shift comparison, so the connecting maps come from
    this same triangle. They are not arbitrary existential sheaf morphisms.

Edge cases: empty U; U = X with empty Z; empty X; zero K; the zero ring;
all integer degrees, including zero and negative degrees; nonreduced Z and
closed ideals not finitely presented. All remain covered. No prime or
characteristic bound occurs. The universe u is bound, and the coefficient
and module universe u+1 is the dependency's established small-etale-site
encoding. Smaller finite rings can be lifted into it. There is no separate
lower test-object universe that could make a hypothesis vacuous.

Independent H4 searches used different queries from the first worker:

- LeanFinder through `msearch.py`: "Etale sheaves localization triangle relative
  pushforward proper support open closed complement" returned eight results,
  including scheme O-module restriction and pushforward. None is this assertion.
- Loogle through `msearch.py`: `"Triangle", "Exact"` returned generic derived
  triangles of short exact complexes, without relative compact support.
- LeanSearch through `msearch.py`: "Distinguished triangle of relative compactly
  supported etale derived direct images for open closed decomposition" was
  unavailable (Internal Server Error); no conclusion is drawn from that failure.
- Direct rg in upstream WeilConjectures, Mathlib, and this project's lean/Sheaf:
  `localization.*triangle|localisation.*triangle|exists_distTriang_openClosed|
  openClosed|open_closed|compactSupport.*triangle`, and independently
  `shriek.*[Tt]riangle|[Tt]riangle.*shriek|shriek.*locali`, plus the full proposed
  declaration name. Read `exists_distTriang_openClosed` in
  `SixFunctors/OpenClosed/Derived.lean`: it is the absolute counit/unit triangle
  on X, without relative pushforward or independently chosen compactifications.
  Read `WeilSheaf.exists_exact_higherLowerShriek_of_openClosed` in
  `DeligneLaumon/Reduction/FormalSteps.lean`: it is a different coefficient
  category over a field, for a sheaf and natural degrees, and only a three-term
  exact sequence. The project's `SmoothConstantLowerShriekLocalization` concerns
  smooth curve assertions, not this statement. None replaces this module.

H5/H6/H8/H9: the module introduces only one named theorem, whose whole proof is
`sorry`; no definition, private notion, file-local notation, or local instance.
Its declaration and module docstrings name Tag 0GKP and the blueprint id. Its
five proof-plan steps follow the node: geometric hypotheses; absolute
recollement; application of the triangulated compact-support functor; comparison
with independent compactifications using composition; homology long exact
sequence. Read the proof-dependency records and checked the imports, including
those supplied transitively. The unstated recollement/composition proof nodes
are named in the docstring and introduce no missing statement-level object.
All lines are at most 100 characters; the sole universe u and all variables are
bound. A direct signature comparison confirms `lean.statement` is verbatim the
file's signature.

Mismatches found: none. Changes: this second-reading report only; the node and
Lean statement are preserved. Independent server-only `scompile.py` validation
passed with no errors or warnings: the delivery module took 1.9 seconds; the
side dependency EtaleConstantModuleDirectImageLeftExact also compiled in the
private overlay (9.5 seconds). Both used nice 19, two threads, 60 seconds per
file. No local Lean compiler or global build was run.
