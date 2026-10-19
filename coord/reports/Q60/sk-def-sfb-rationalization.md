## Worker report

Existing definition: `CategoryTheory.Rationalization`, in
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.Rationalization`.
No module is added: the canonical construction and all its asserted properties already
exist. The node's `lean.declarations` records the supporting declarations in that module,
including `algebraMap_smul` so that compatibility is recorded explicitly. Only the item's
`lean` field changes; no statement correction, new node, or dependency repair is needed.

I read the current main-20261015 blueprint `_section.md` and proof paragraph of
`sec-proetale-coefficients/sk-def-sfb-rationalization`, all four statement dependencies and
the two remaining proof dependencies, their recorded Lean declarations, the example compact
object module and node, and the stage brief and delivery rules. There is no repair note for
this item. The source was read in the read-only slopmaster2 checkout and retrieved again with
`scompile.py --source WeilConjectures.CategoryTheory.DerivedCategory.Complete.Rationalization`;
the retrieved construction and properties agree with that source.

Clause-by-clause correspondence (names below are in `CategoryTheory`, and component names
are in `CategoryTheory.Rationalization`):

- A commutative ring R is `{R : Type w} [CommRing R]`. An arbitrary submonoid is
  `(M : Submonoid R)`, without nonzero, cancellative, or nontrivial assumptions.
- The category is `(C : Type u) [Category.{v} C] [Preadditive C] [Linear R C]`.
  Its triangulated structure is `[HasZeroObject C] [HasShift C ℤ]`, additive integer
  shifts, `[Pretriangulated C] [IsTriangulated C]`; R-linear shifts are
  `[∀ n : ℤ, (shiftFunctor C n).Linear R]`. These are precisely the ambient hypotheses
  under which the quotient's properties are used. The underlying category construction
  itself requires fewer assumptions because Lean drops unused section variables; no
  property of its triangulation or scalar invertibility is asserted without the full
  ambient hypotheses.
- “X is M-torsion” is `torsion M C X`, defined by `∃ m ∈ M, m • 𝟙 X = 0`.
  This is the exact declaration recorded by `def-sfb-torsion-objects`.
- “Morphisms whose mapping cone is M-torsion” is `W M C := (torsion M C).trW`,
  the declaration recorded by `def-sfb-rationalization-morphisms`. Mathlib's `trW`
  expands to `∃ (Z : C) (g : Y ⟶ Z) (h : Z ⟶ X⟦1⟧),
  Triangle.mk f g h ∈ distTriang C ∧ torsion M C Z`, with the distinguished-triangle
  condition actually represented by a dependent existential binder. Thus these are
  precisely the cone-torsion arrows, with no chosen cone or extra cone hypothesis.
- “The rationalization is the Verdier quotient, i.e. the localization at these arrows”
  is the existing reducible definition
  `def Rationalization : Type _ := (Rationalization.W M C).Localization`.
  This is the same `MorphismProperty.Localization` construction named by the Mathlib
  match of `def-sfb-rationalization-quotient`, specialized to the recorded W.
- “It is triangulated” uses `instIsTriangulatedTorsion` together with Mathlib's
  `ObjectProperty.trW` calculus-of-fractions and triangulation-compatibility instances,
  then `Triangulated.Localization.instPretriangulatedLocalization` and
  `Triangulated.Localization.instIsTriangulatedLocalization`. These apply to the very
  same quotient by definitional reduction, rather than an equivalent category chosen
  separately. `instIsTriangulatedTorsion` is the recorded declaration of
  `lem-sfb-torsion-triangulated`.
- “The localization functor is triangulated” is `Q M C := (W M C).Q`, with its upstream
  instance `(Q M C).IsTriangulated`, supplied by
  `Triangulated.Localization.isTriangulated_functor`. Its localization instance also
  synthesizes against exactly `W M C`.
- “Every m in M acts invertibly” is `isIso_smul_id (hm : m ∈ M)
  (Y : Rationalization M C) : IsIso (m • 𝟙 Y)`. This covers every quotient object,
  not merely objects presented syntactically as `Q.obj X`.
- “Linear over every localization A of R at M” is
  `linear (M : Submonoid R) (C : Type u) (A : Type w') [CommRing A] [Algebra R A]
  [IsLocalization M A] : Linear A (Rationalization M C)`. The type and morphism
  universes of C and the universes of both rings are independent. The construction
  is `Linear.ofRingMorphism (toCatCenter M C A)`, where `toCatCenter` uses the
  localization universal map on the original R-action. It is actual data, not a
  choice from an unproved existence assertion. Taking A to be `Localization M`
  gives the particular ring R[M⁻¹].
- “Compatibly with its R-linear structure” is `algebraMap_smul`:
  `algebraMap R A r • f = r • f` for every r and every morphism f of the quotient.
  The recorded dependency `def-sfb-rationalization-linear` also states existence and
  uniqueness for this same `Rationalization M C`, in module
  `Sheaf.CategoryTheory.RationalizationLinear`, declaration
  `CategoryTheory.Rationalization.isIso_smul_id_and_existsUnique_linear`.
  I read its full signature and docstring. Uniqueness is additional to the present
  unit's wording; this item records the already existing compatible structure and
  does not introduce another one or restate that theorem.
- The notation T[ℓ⁻¹] for M = {ℓⁿ} is `Rationalization (Submonoid.powers ℓ) C`.
  This is specialization of the existing definition; no second category definition
  or file-local notation is introduced.

Proof-dependency interfaces were also checked: the upstream
`smul_id_cone_eq_zero` says every distinguished cone of `m • 𝟙 X` is killed by m*m,
not merely one chosen cone. `W_smul_id` then proves membership for m in M; these
are the two recorded declarations of `lem-sfb-smul-id-in-w`. Together with the
triangulated torsion property these are precisely the steps of the unit's source
proof. No proof or new theorem is written in this delivery.

Edge cases checked mathematically and against the signatures:

- M = {1}: torsion means the identity vanishes, hence the zero objects; the quotient
  inverts precisely the arrows with zero cone. No unwanted nontriviality hypothesis.
- 0 in M, including powers of ℓ = 0: every object is torsion and the quotient is a
  zero category. No `0 ∉ M` assumption; localizations at such M are zero rings, and
  the center construction and `IsLocalization` interface still apply.
- R itself a zero ring and C a zero category are included. Since the identity is
  already zero in the corresponding linear setting, there is no incompatible demand
  that a nonzero scalar stay nonzero.
- Powers of ℓ = 1 give the {1} case; ℓ need not be prime or nonzero. Both powers-of-zero
  and powers-of-one categories elaborate in the compile probe.
- A has independent universe w', so arbitrary localization models and the standard
  fraction localization are allowed; there is no equality imposed between u, v, w,
  and w'. An empty category cannot satisfy the stated zero-object assumption,
  as is intrinsic to the source's triangulated-category hypothesis.

Searches for existing notions and declarations:

1. `msearch.py ... leanfinder "rationalization of an R-linear triangulated category as
   the Verdier quotient by M-torsion objects"`: eight generic triangulated-localization
   results, including `Triangulated.Localization.instIsTriangulatedLocalization` and
   `isTriangulated_functor`; none defines the specialized rationalization in Mathlib.
2. `msearch.py ... leansearch "rationalization of a linear triangulated category by
   inverting a submonoid"`: eight results, including the generic triangulated
   localization instances and unrelated monoid localizations; no exact Mathlib notion.
3. `msearch.py ... loogle "IsLocalization, Linear"`: unknown identifier `Linear`;
   inconclusive, not evidence of absence. The corrected query `CategoryTheory.Linear`
   returned twelve declarations, including the category-linear structure and
   `Linear.homModule`; no specialized rationalization.
4. `msearch.py ... grep "Rationalization|rationalization|Verdier quotient"
   CategoryTheory`: one hit, a Verdier-quotient mention in
   `Mathlib/CategoryTheory/Triangulated/LocalizingSubcategory.lean:19`.
5. `rg` of the full read-only `WeilConjectures` tree for
   `def Rationalization|namespace CategoryTheory.Rationalization|def torsion :
   ObjectProperty|sk-def-sfb-rationalization` located the existing exact construction
   at `CategoryTheory/DerivedCategory/Complete/Rationalization.lean:161` and its
   supporting definitions and functoriality file. The literal blueprint id has no
   separate upstream hit. Reading the whole module, rather than searching only its
   name, establishes all the clause correspondences above.
6. `rg` of `lean/Sheaf` found `CategoryTheory/RationalizationLinear.lean`, the recorded
   existence/uniqueness theorem, and a distinct scalar-localization family. No duplicate
   of the canonical Verdier quotient is needed. Searching
   `dag/lean_names_upstream.json` for `CategoryTheory.Rationalization` returned no hit;
   this index is stale for the current source and was not used to reject the match.
7. Direct source inspection of Mathlib `Localization/Construction.lean`,
   `Triangulated/Subcategory.lean`, and `Localization/Triangulated.lean` confirmed the
   `Localization`, `Q`, `trW`, and triangulated-category interfaces of the quotient
   dependency's `mathlib_match`.

No STATEMENT-DISPUTED flag or node fault. In particular this is not a unit statement
correction: the node is unchanged, and its existing construction is being bound to all
of its already present supporting declarations.

Validation: the sandbox scratch probe `scratchpad/ExistingProbe.lean` is not a delivered
module. It checks all nine names with `#check @...`, and uses fully explicit variables
with `autoImplicit false` to check synthesis of the quotient's triangulated structure,
its R-linear structure, its A-linear structure, and Q's triangulated/localization
instances. The probe uses `noncomputable section` because the existing localization
linear structures are noncomputable. It is compiled only by the prescribed scompile.py
wrapper. The required deliver2.py --no-push run additionally checks every recorded
existing declaration and runs server preflight. No library files are edited.

## Second reading by Q60

I independently opened the node, its `_section.md` source, the separate proof file,
and the slopmaster2 source module. The node introduces a commutative ring `R`, an
`R`-linear triangulated category `T` with `R`-linear integer shifts, and a submonoid
`M ≤ R`; it defines `M`-torsion objects, the Verdier localization at arrows with
`M`-torsion mapping cone, and the notation `T[M⁻¹]` (with `T[ℓ⁻¹]` for powers of
`ℓ`). Its conclusion has exactly these clauses: the quotient is triangulated, the
localization functor is triangulated, each `m ∈ M` acts invertibly, and the quotient
has a compatible linear structure over every localization of `R` at `M`.

The Lean rendering matches item by item. `R` and `M` are the `CommRing R` and
`Submonoid R` parameters. The category and hypotheses are the `Category`, `Preadditive`,
`Linear R`, `HasZeroObject`, `HasShift ℤ`, additive and `Linear R` shift instances,
`Pretriangulated`, and `IsTriangulated` parameters used by the listed declarations.
`Rationalization.torsion` is exactly `∃ m ∈ M, m • 𝟙 X = 0`; `Rationalization.W` is
the `trW` mapping-cone class; and `Rationalization` is exactly
`(Rationalization.W M C).Localization`. `Rationalization.Q` is the canonical
localization functor and has the triangulated-functor instance. `isIso_smul_id`
quantifies over every quotient object and every `m ∈ M`. `linear` accepts an
arbitrary `A` with `CommRing A`, `Algebra R A`, and `IsLocalization M A`, and
`algebraMap_smul` gives the stated compatibility. Powers of `ℓ` are represented by
`Submonoid.powers ℓ`. The definition's reduced type omits unused section instances,
but the supporting property declarations retain exactly the source hypotheses; this
is Lean elaboration, not a stronger or weaker mathematical statement.

I found no mismatch and changed no Lean or node content. The dependency records for
torsion objects, cone morphisms, the quotient, and localized linearity were opened;
each is the notion used by the corresponding clause. The proof paragraph maps to the
triangulated torsion instance, `W_smul_id`, the quotient localization instances, and
the localized linear structure, with no extra proof claim.

Edge cases checked are `M = {1}`, `0 ∈ M` (including `Submonoid.powers 0`), a zero
coefficient ring, a zero category, `Submonoid.powers 1`, and independent ring/category
universes. No nonzero, prime, cancellative, finiteness, Noetherian, or universe-equality
hypothesis appears. The scratch probe compiled both powers cases and synthesized the
triangulated, localization, `R`-linear, and arbitrary-`A`-linear structures.

My independent searches used `msearch.py leanfinder` with query "localizing a category
by cones annihilated by scalars" (eight generic localization-linearity and shift
results); `leansearch` with query "invert scalars in a triangulated category by killing
objects annihilated by a multiplicative set" (eight generic localization,
triangulation, and scalar-isomorphism results); and `loogle` with
`IsLocalization, CategoryTheory.Linear` (zero hits). I also used `rg` for `annihilat`,
`torsion`, `CatCenter`, `ofRingMorphism`, `IsLocalization`, and `smul_id_cone` across
Mathlib localization/subcategory modules, slopmaster2's complete derived-category
modules, and the project's category-theory modules. These locate the exact existing
upstream construction, the generic Mathlib interfaces, and the project's recorded
uniqueness wrapper. I read `trW`, `MorphismProperty.Localization`, `Q`, and the
triangulated-localization instances directly. No duplicate module or new definition
node is needed. Both upstream and dependency sources were also retrieved with
`scompile.py --source`. The probe
`scompile.py Q60 sk-def-sfb-rationalization scratchpad/ExistingProbe.lean`
completed cleanly, with no errors or warnings. The report is the only second-reader
change.
