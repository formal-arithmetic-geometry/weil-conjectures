## Worker report

The module `Sheaf.AlgebraicGeometry.ProperDerivedDirectImageCoproducts` states
`AlgebraicGeometry.Etale.proper_rightDerivedLowerStar_preservesCoproducts`.
Its only proof is `sorry`. No definitions, new nodes, dependency modules, or statement
corrections were needed.

Read the complete item and all five statement dependencies, including their Lean records,
and the declarations and docstrings those records identify. Read the blueprint source
`sec-smooth-purity/sk-prop-sf-cbc/lem-amb-proper-coproducts.md` (order 1562).
The node already supplies the finite coefficient hypothesis needed by that proof.

Hypothesis and clause correspondence:

- The finite commutative ring A is `(A : Type (u + 1)) [CommRing A] [Finite A]`.
  No nontriviality or invertibility condition is imposed.
- The schemes and their morphism are `{V T : Scheme.{u}} (r : V ⟶ T)`.
- Properness is `[IsProper r]`. This includes local finite type, and universal
  closedness implies quasi-compactness, hence finite type. There is no additional
  locally-finite-type or quasi-compact-morphism assumption.
- Both Noetherian hypotheses are rendered separately as `[IsLocallyNoetherian V]`
  and `[CompactSpace V]`, and `[IsLocallyNoetherian T]` and `[CompactSpace T]`.
  CompactSpace has no Hausdorff requirement.
- Ordinary unbounded D(V_et,A) and D(T_et,A) are the domain and codomain of
  `rightDerivedLowerStar (ModuleCat.{u + 1} A) r`. Its definition is exactly
  `(lowerStar (ModuleCat.{u + 1} A) r).rightDerivedFunctor`, on the full derived
  categories of `Sheaf _.smallEtaleTopology (ModuleCat.{u + 1} A)`, definitionally
  the recorded `DerivedCategoryModule A _`. No constructibility or boundedness
  predicate is imposed.
- Preservation of arbitrary set-indexed coproducts is the first conjunct:
  `∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) ...`.
  The index universe is the coefficient modules' universe, covering all small
  sets for these sheaf categories. It is not restricted to finite or countable I.
  PreservesColimitsOfShape says the image of every colimit cocone of that shape
  is again a colimit cocone; for discrete diagrams this is precisely invertibility
  of the canonical coproduct comparison induced by the coprojections.
- The final bounded-below clause is the second conjunct, `Nonempty` of a natural
  isomorphism `rightDerivedLowerStarPlus ... ⋙ DerivedCategory.Plus.ι ≅
  DerivedCategory.Plus.ι ⋙ rightDerivedLowerStar ...`.
  Thus this identifies the functors naturally on the entire bounded-below category,
  rather than merely asserting unrelated objectwise isomorphisms.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`,
  read with its source scheme and morphism binders and its parent classes.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`.
- `Sheaf.AlgebraicGeometry.DerivedCategories`: the existing ordinary-category
  encoding, imported publicly; `AlgebraicGeometry.Etale.DerivedCategoryModule`
  is the abbreviation from its public upstream import
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar` (objectwise evaluation on the fibre product).
  The direct-image node also records `rightDerivedLowerStarPlus`; its actual
  source file is `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`,
  explicitly imported publicly. That file also gives `rightDerivedLowerStar`.
  These use the same underived lowerStar and the generic derived functors, so
  no dependency replacement is necessary.

Proof-only imports are the recorded modules for
`def-weil-pbc-torsion-etale-sheaf`,
`lem-sbc-higher-direct-image-forget-comparison`, `pqf-lem-proper-basic`, and
`src-right-derived-functor-plus-compatibility`.
Read the proof dependencies' statements and available signatures. The three proof
nodes `lem-fin-finite-type-fibre-dimension-bound`, `lem-kun-proper-torsion-cd-bound`,
and `lem-exc-direct-image-coproducts` have no recorded modules yet and therefore
cannot be imported; their exact roles remain in the theorem docstring.
The compatibility declaration read is
`CategoryTheory.Functor.rightDerivedFunctorPlusCompatibility`, in
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility`.

Edge cases checked mathematically: I empty is included (initial/zero object), as are
infinite sets and arbitrary unbounded complexes. The zero ring is allowed by CommRing
and Finite. Empty schemes satisfy the same scheme hypotheses; no point is required.
Neither absolute finite dimension, torsion-order invertibility, a ground field, nor a
constructibility restriction was introduced. The fibre bound used in the proof allows
empty fibres. No node fault or disputed statement was found.

Searches made before drafting:

- msearch.py leanfinder: `proper derived direct image of etale module sheaves preserves
  arbitrary coproducts`; eight hits, including sheaf/condensed colimit interfaces and
  monoidal sheafification, no exact theorem about proper ordinary derived pushforward.
- msearch.py loogle: `"rightDerivedFunctor", "PreservesColimitsOfShape"`; zero hits.
- msearch.py leansearch: `proper derived pushforward of finite coefficient etale sheaves
  preserves coproducts`; service unavailable (Internal Server Error), not a negative match.
- msearch.py grep in CategoryTheory: `proper.*[Cc]oproduct|[Cc]oproduct.*proper|rightDerived.*coproduct`;
  23 incidental hits about morphism properties and coproducts, no exact theorem.
- rg on upstream WeilConjectures and this project's lean/Sheaf for the node id,
  `proper.*[Cc]oproduct|[Cc]oproduct.*proper`, and derived lower-star names;
  no exact declaration. Upstream ProjectionFormula mentions the distinct
  `lem-amb-proper-coproducts-projection`; UpperShriek discusses coproducts in prose.
  The project's ProperPerfectRightAdjointCoproducts concerns O_X-modules and a
  different right adjoint. None states this node.
- rg of `dag/lean_names_upstream.json` for the item and proposed full declaration name:
  no hits. Read the actual upstream derived-functor definitions rather than copying
  any notion.

Validation: scompile.py compiled the delivered file cleanly on the server in 2.7 seconds,
with nice 19, two threads, and a 60-second per-file limit. No local compiler was run.

## Second reading by NF

I read the sandbox node and proposed module independently, the five statement
 dependency records and their actual declarations, the blueprint source at order
1562, and Stacks morphisms.tex lemma-morphism-finite-type-bounded-dimension (0A3V)
and etale-cohomology.tex lemma-cohomological-dimension-proper (095U) and
lemma-finite-cd-mod-n-direct-sums (0F11). The latter is the Z/n version of the
finite-ring criterion cited by the node; it introduces no invertibility condition.
The reviewed stage-1 node already resolves the blueprint's unspecified A as a
finite commutative ring. No further natural-language correction is required.

The second reading found an existing exact project statement that the worker
missed: Sheaf.AlgebraicGeometry.ProperDerivedDirectImageCoproducts already contains
AlgebraicGeometry.Etale.proper_rightDerivedLowerStar_preservesCoproducts, landed
by NP (coord/ledger.md, 2026-10-15 06:44 UTC). I opened its complete declaration,
docstring and NP's report. The current node lacks its Lean record after DAG sync,
but the source module is present. I removed the duplicate sandbox module and
recorded the existing declaration, branch newtargets-dag, existing: true. Its
signature is copied verbatim into lean.statement. The worker report above is
preserved as the historical report of the initial draft, not the final inventory.

Node checklist, with the final existing Lean rendering and verdict for each item:

1. Object A, finite commutative coefficient ring: `(A : Type (u + 1))
   [CommRing A] [Finite A]`. Match; neither a field nor a nonzero ring is required.
2. Objects V and T, schemes, and their morphism r: `{V T : Scheme.{u}}
   (r : V ⟶ T)`. Match; no ground field or additional structure morphism.
3. Properness and finite type: `[IsProper r]`. Match. I read IsProper in
   Mathlib.AlgebraicGeometry.Morphisms.Proper: it extends IsSeparated,
   UniversallyClosed and LocallyOfFiniteType. The instance in UniversallyClosed
   supplies QuasiCompact, so this is finite type as the dependency defines it.
4. Noetherian V: `[IsLocallyNoetherian V] [CompactSpace V]`. Match.
   Noetherian T: `[IsLocallyNoetherian T] [CompactSpace T]`. Match.
   The local class requires Noetherian sections on every affine open, equivalent
   to the recorded affine-cover definition; CompactSpace means IsCompact univ,
   with no Hausdorff condition. Both are precisely the dependency notions.
5. Ordinary unbounded D(V_et,A) and D(T_et,A), and total Rr_*:
   `rightDerivedLowerStar (ModuleCat.{u + 1} A) r`. Match. I opened
   Sheaf.AlgebraicGeometry.DerivedCategories and upstream Derived.Coefficients:
   DerivedCategoryModule is DerivedCategory of ModuleCat-valued small-etale
   sheaves. I opened UpperLowerStar.Defs: lowerStar evaluates F on W ×_T V.
   UpperLowerStarCoherence defines rightDerivedLowerStar as lowerStar's
   rightDerivedFunctor on those full unbounded derived categories. There is
   no boundedness, torsion-cohomology or constructibility predicate on inputs.
6. Every set-indexed coproduct is preserved: `∀ I : Type w,
   PreservesColimitsOfShape (Discrete I) (rightDerivedLowerStar ... r)`.
   Match. The landed declaration has explicit independent universe w, improving
   on the draft's fixed Type (u + 1). This quantifies over all diagrams and
   colimit cocones of that discrete shape, exactly the canonical comparison
   being invertible whenever the coproduct exists. It does not assert existence
   of coproducts too large for the category. Small coproducts are all included.
7. Bounded-below restriction agrees with the recorded derived direct image:
   `Nonempty (rightDerivedLowerStarPlus ... r ⋙ DerivedCategory.Plus.ι ≅
   DerivedCategory.Plus.ι ⋙ rightDerivedLowerStar ... r)`. Match; this is a
   natural functor isomorphism. I read the Plus definition in Coherence:
   it is lowerStar.rightDerivedFunctorPlus, the recorded direct-image notion.
   I also read rightDerivedFunctorPlusCompatibility and its source hypotheses:
   additive functor, enough injectives and K-injective resolutions, supplied
   by the existing Grothendieck sheaf-category infrastructure. These are not
   additional geometric assumptions on r, V or T.

Edge cases: Empty index types are permitted and include the initial/zero object
comparison. Zero complexes, empty schemes and empty fibres are not excluded.
The zero ring is allowed (no Nontrivial instance). There is no n binder in the
statement; the proof allows fibre bound e = 0 and torsion exponent N = 1.
No characteristic or invertibility condition occurs. Universes u and w are
explicitly bound; the coefficient universe follows the recorded six-functor
small-etale encoding. No auto-implicit variable, private notion, local instance,
local notation, new definition, new node, or dependency replacement is needed.
The existing theorem has only sorry as proof. Its docstring names the source
and blueprint and follows all three node proof steps, including the lcm torsion
argument, coefficient-forgetting comparison and final Plus compatibility.
I opened the available proof modules ProperBasic, HigherDirectImageForgetComparison
and PlusCompatibility as well; the other proof steps remain named in the docstring.

Independent searches, using different terms from the first worker:

- msearch LeanFinder: `derived pushforward along a proper scheme map commutes
  with infinite direct sums`: eight hits, ordinary structure-sheaf pushforward
  and sheaf module composition results, none the proper etale derived theorem.
- msearch Loogle: `"PreservesColimitsOfShape", "Sheaf"`: ten hits about general
  presheaf/sheaf colimits and extensive topologies, none this statement.
- msearch LeanSearch: `proper pushforward finite coefficient sheaves unbounded
  derived category direct sums`: Internal Server Error, recorded unavailable.
- Independent rg over Mathlib for derived/coproduct and proper/coproduct pairs
  found only unrelated coproduct interfaces. Independent rg over upstream
  WeilConjectures, project lean/Sheaf and dag/lean_names_upstream.json for
  lowerStar/coproduct, pushforward/direct sums and the exact node/name found
  the existing project theorem described above. Upstream ProjectionFormula's
  lem-amb-proper-coproducts-projection is a different statement.

Mismatch repaired: H4 duplicate of a landed declaration; dropped the draft and
reused the existing theorem. Its arbitrary index universe also resolves the
unnecessary restriction in the draft. No node statement, proof or dependency
field was changed. Final delivery contains only the existing Lean record and
this report, with no Lean module to replace or recompile. deliver2.py validates
the existing declaration through an actual server #check using scompile.py.
