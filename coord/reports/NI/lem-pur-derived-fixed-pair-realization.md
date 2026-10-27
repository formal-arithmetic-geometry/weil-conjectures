## Worker report

The module `Sheaf.CategoryTheory.DerivedFixedPairRealization` states
`CategoryTheory.Endofunctor.IsoAlgebra.derivedFixedPairRealization`, with exactly one
postponed theorem and six transparent abbreviations for its subcategories and restrictions.
The theorem's docstring contains the node's nine-step proof. No theorem is proved and no
definition has postponed data. The node's mathematical statement is unchanged.

Hypothesis and clause correspondence:

- The abelian category is `{A : Type u} [Category.{v} A] [Abelian A]`, with
  `[IsGrothendieckAbelian.{v} A]`. The ordinary derived categories have independently
  chosen morphism universes `[HasDerivedCategory.{w} A]` and
  `[HasDerivedCategory.{wB} (IsoAlgebra P)]`; no equality of universes is imposed.
- The additive exact autoequivalence is `(P : A ⥤ A) [P.Additive] [P.IsEquivalence]`.
  An equivalence preserves finite limits and colimits, so exactness is inferred rather
  than an additional assumption. The inverse functor is `P.inv`.
- The strictly full subcategory is `S : ObjectProperty A` with
  `S.IsClosedUnderIsomorphisms`. Its zero, kernel, cokernel and extension conditions are
  respectively `S.ContainsZero`, `S.IsClosedUnderKernels`,
  `S.IsClosedUnderCokernels`, `S.IsClosedUnderExtensions`.
- Preservation by P and its inverse is precisely `hPS` and `hPinvS`.
- B and U are the recorded `IsoAlgebra P` and `forget P`. Their abelian and exact
  structures are the upstream instances publicly imported by the recorded created-abelian
  module. No replacement abelian structure or arbitrary exact functor is introduced.
- C is `fixedPairRealizationTarget S`, exactly `homologyProperty S ⊓ t.bounded`.
  D is `fixedPairRealizationSource P S`, exactly
  `homologyProperty (S.inverseImage (forget P)) ⊓ t.bounded`. Thus the source condition
  is on the underlying cohomology objects, not on terms of a representative.
- Restriction of the standard t-structures is expressed without choosing extra structure:
  both full subcategories are triangulated, and both are stable under every `t.truncLE n`
  and `t.truncGE n`. These give the induced standard t-structures through
  `ObjectProperty.HasInducedTStructure.mk'` (Mathlib's Induced interface). Their halves
  are the inverse images of the ambient halves, their orthogonality is inherited,
  and boundedness is already in the defining predicates. The source and target heart
  abbreviations use exactly these inverse-image standard hearts.
- The existential proofs `hP` and `hU` assert that the actual functors
  `P.mapDerivedCategory` and `(forget P).mapDerivedCategory` preserve the required
  predicates. The action and forgetful restrictions use `ObjectProperty.lift`; their
  objects and maps are the actual derived objects and maps.
- The next universally quantified cochain equation characterizes Theta on `Q.obj K`
  by both exact-functor factorization isomorphisms and `Q.map` of the termwise
  `strNatIso P`. In diagrammatic composition order it is
  `Theta_QK ≫ a_U = D(P)(a_U) ≫ a_P ≫ Q(C(t))`.
  This is the node's formula after multiplying its last comparison to the left side.
- Theta itself is the existing natural isomorphism `cyclicDerivedStructure P`, obtained
  by localization, not an arbitrary action or chosen natural isomorphism. Naturality
  is part of its type, and the cochain formula specifies descent through localization;
  quasi-isomorphisms are inverted by `DerivedCategory.Q`.
- The shift equation, quantified over every object and every integer n, is exactly
  `Theta_K[n] ≫ sigma_U = D(P)(sigma_U) ≫ sigma_P ≫ Theta_K[n]` with the first
  Theta evaluated at the shifted object. All comparisons are the canonical
  `mapDerivedCategory.commShiftIso` maps, so identity and iterated-shift coherence are
  those of these already defined comparison structures.
- R has domain D and codomain `IsoAlgebra (fixedPairRealizationAction P S hP)`.
  The equality `R ⋙ forget ... = fixedPairRealizationForget ...` specifies both its
  underlying objects and its underlying maps. The `HEq` clause specifies that its
  structure maps are precisely Theta. Heterogeneous equality only accounts for the
  endpoint equalities supplied by the preceding functor equality; it changes no map.
  These two clauses determine R rather than merely requesting an unconstrained functor.
- `hR` asserts that the same R sends the entire source heart to pairs whose carriers
  are in the target heart. `IsEquivalence` is asserted for its actual restriction,
  constructed by `ObjectProperty.lift`, not for an unrelated heart equivalence.
- The extension is an arbitrary `E : ShortComplex (IsoAlgebra P)` with
  `hE : E.ShortExact`. All three carrier conditions are explicitly present.
  `¬ Nonempty E.Splitting` means nonsplit in B;
  `Nonempty (E.map (forget P)).Splitting` means split after U.
- Its canonical connecting map is Mathlib's `hE.singleδ`, with endpoints
  `E.X₃[0]` and `E.X₁[0][1]`. The conclusions assert that this exact map is nonzero
  and its actual derived-forgetful image is zero. They also assert `¬ R.Faithful`.
  Finally X and Y exhibit its endpoints inside D, and invertible endpoint comparisons
  eX and eY transport this very connecting map to a D-morphism whose R-image is zero.
  This is R(delta)=0; zero and nonzero are invariant under those endpoint isomorphisms.

Dependencies read and used:

- `def-sp-grothendieck-abelian`: Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic,
  `CategoryTheory.IsGrothendieckAbelian`, including the derived small-limit/colimit instances.
- `def-weil-abstract-derived-category`: Mathlib.Algebra.Homology.DerivedCategory.Basic,
  `HasDerivedCategory`, `DerivedCategory`, and `DerivedCategory.Q`.
- `def-weil-endofunctor-fixed-pair-category`:
  WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra,
  `CategoryTheory.Endofunctor.IsoAlgebra`, `.forget`, `.str`, `.strNatIso`.
- `lem-sf-fixed-pair-created-abelian-structure`:
  Sheaf.CategoryTheory.FixedPairCreatedAbelianStructure,
  `IsoAlgebra.fixedPairCreatedAbelianStructure`, and its publicly imported upstream
  `IsoAlgebra.abelian` and exact forgetful instances. The complete theorem and the
  signatures/docstrings of the actual instance interfaces were read.
- `def-weil-t-structure`: Mathlib.CategoryTheory.Triangulated.TStructure.Basic and Heart,
  `TStructure`, `.bounded`, `.heart`.
- `def-sbc-standard-tstructure-derived-category`:
  Mathlib.Algebra.Homology.DerivedCategory.TStructure, `DerivedCategory.TStructure.t`.
- Added the already landed definition node `def-sf-cyclic-derived-hom-data` to stmt_deps.
  It owns `IsoAlgebra.cyclicDerivedStructure` (its recorded `lean.declaration`) in
  Sheaf.CategoryTheory.CyclicDerivedHomData. The exact-sequence theorem is not needed.
  Read the actual definition: it is
  `(mapDerivedCategoryCompIso U P).symm` followed by the derived image of the
  natural structure isomorphism. A transitive stmt_deps/proof_deps traversal confirms
  that this added dependency does not depend on the present item.
- Proof interfaces are the recorded Mathlib exact-functor factorization, cohomology,
  localization, single-full-faithfulness, concentrated-single, single-triangle and
  map-of-single-connecting-map declarations. The module publicly gets their statement
  interfaces through its imports and privately imports the stated proof module
  Sheaf.Paper.CohomologyInWeakSerreSubcategory and Mathlib's Ext.Map.

Edge cases checked: S containing only zero; the zero category; P the identity;
zero objects and zero connecting morphisms; arbitrary positive, zero and negative shifts;
the zero/empty cohomological-support case; bounded objects not supplied with a fixed
interval; arbitrary derived localization universes. A split extension in B does not
satisfy the nonsplitting premise. An extension not split after U is not claimed to be
killed. For the Jordan extension the premises give the expected nonfaithfulness while
leaving the degree-zero heart restriction an equivalence. No unconditional failure of
faithfulness is asserted when no such extension exists.

Searches (2026-10-26):

- msearch LeanFinder, `Exact autoequivalence fixed pair derived realization functor
  equivalence on hearts nonfaithful`: eight related exact-functor/single/Ext declarations,
  no theorem giving the complete statement.
- msearch Loogle, `IsoAlgebra, mapDerivedCategory, TStructure.heart`: zero matches;
  IsoAlgebra is an upstream project name outside Loogle's Mathlib index.
- msearch LeanSearch, `derived category fixed pairs exact autoequivalence equivalence
  on hearts`: eight derived-category/triangulated/Ext declarations, no complete match.
- msearch grep, `IsoAlgebra|mapDerivedCategory` in CategoryTheory: no matches.
- msearch grep, `singleδ|mapDerivedCategorySingleFunctor|mapDerivedCategoryFactors`
  in Algebra/Homology/DerivedCategory: sixteen matches confirming the canonical
  factorization, single comparison and connecting-map interfaces.
- rg in lean/WeilConjectures and lean/Sheaf for fixed-pair names, derived realization,
  homologyProperty and weak-Serre names found the upstream fixed-pair category,
  cyclicDerivedStructure, and homologyProperty; they are reused. Exact declaration-name
  searches for derivedFixedPairRealization and fixedPairRealization returned no matches.
  The required node-id search in lean/WeilConjectures found no existing statement.

No statement dispute, no correction, no dependency repair and no new node is needed.
The withdrawn compact-object example and its node were read: the current node binds
the upstream compact-object declaration, so its withdrawn file is not copied as an API.

Validation: the final module passed scompile.py both as sandbox and as its library module
in 2.8 and 2.9 seconds, respectively, with no reported warning or error. All declarations
have blueprint/source docstrings and all lines are at most 100 characters.

## Second reading by NI

I performed a separate second pass with the full node statement and final Lean file open.
No second agent was started, as the dispatcher explicitly prohibits that; the maintainer's
independent delivery review remains separate. I checked each premise and conclusion using
the correspondence above, in particular all three carrier conditions, closure under zero,
the inverse-auto-equivalence premise, the entire heart restriction, both comparison maps
in the cochain formula, the order of the three shift factors, and the canonical rather
than arbitrary extension boundary. The last R-image clause was tightened from equality
with R(0) to literal equality with zero, and the revised file compiled cleanly.
The t-structure claim is expressed by triangulated closure and stability under the
canonical good truncations, the standard sufficient and necessary restriction interface;
the hearts are explicitly the inverse images of the ambient standard hearts. No hidden
equivalence D(S) ≃ C or D(S_B) ≃ D, faithfulness premise, representative choice,
extra t-structure, or finite cohomological interval is assumed.

## Returned delivery repair

H2, returned head `70a373243cad`: replaced the unnecessary theorem dependency
`lem-sf-cyclic-derived-hom-exact-sequence` with its definition owner
`def-sf-cyclic-derived-hom-data`. Read that node's statement and full Lean record and
re-read `cyclicDerivedStructure` in `Sheaf.CategoryTheory.CyclicDerivedHomData`.
Updated `lean.note` and the dependency paragraph above to name the actual owner.
The Lean module and `lean.statement` are unchanged. Compared the retained delivery
node against current main: before repair, only `stmt_deps` and `lean` differed.
No other node fields are changed. This second reading specifically checks H2: the
new dependency's recorded primary declaration is exactly the definition used by the
module; the exact-sequence theorem's conclusion is not used.
