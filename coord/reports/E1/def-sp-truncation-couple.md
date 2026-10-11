## Worker report

Module: `lean/Sheaf/CategoryTheory/TruncationCouple.lean`. Main declaration:
`CategoryTheory.truncationCouple`. It constructs the two bigraded families and their
three canonical structure maps, as a dependent pair followed by a triple of maps.
No statement correction, new node, or dependency replacement is needed.

The blueprint source was read in full on the server (the local literature copy is
absent): `literature/blueprint/master/blueprint/sec-abelian-varieties/`
`sk-prop-av-pqf-finite/def-sp-truncation-couple.md`, order 520. It agrees with the DAG
statement verbatim. All four statement dependencies and their recorded declarations
and docstrings were read, including the complete initial exact-couple structure.

Hypothesis and clause correspondence:

- The two categories A and B are arbitrary `Type u₁`, `Type u₂` with independent
  hom universes `v₁`, `v₂`, instances `Category`, `Abelian`, and
  `IsGrothendieckAbelian.{v₁} A`, `IsGrothendieckAbelian.{v₂} B`. This is exactly
  the Grothendieck condition at each category's hom universe, as its dependency
  record specifies. Standard derived categories are installed locally in the
  main construction, rather than required as additional hypotheses.
- The functor v is `(F : A ⥤ B)` with `[F.Additive]` and `[PreservesFiniteLimits F]`,
  the recorded additivity and left-exactness notions of def-sp-left-exact-additive.
  Ordinary `Functor.rightDerived n` is not applied to a complex.
- Bounded-below K is `(K : CochainComplex.Plus A)`. The integer a and its
  cohomological vanishing hypothesis are `(a : ℤ)` and
  `ha : ∀ q : ℤ, q < a → IsZero (K.obj.homology q)`. This does not impose
  termwise vanishing below a; the existing Plus hypothesis provides an independent
  termwise lower bound. The construction records ha as an input and does not use
  it to restrict the range of p or q.
- The truncation complex is Mathlib's `K.obj.truncLE q`, bundled in Plus by
  `TruncationCouple.truncation`. Its boundedness proof is the named theorem
  `truncLE_plus`, never a sorry inside a definition.
- The complex H^q(K)[-q] is `(CochainComplex.singleFunctor A q).obj
  (K.obj.homology q)`, bundled as `cohomologyComplex`. A single complex in degree q
  is the standard representative of the degree-zero cohomology object shifted by
  -q. It remains a complex, including for negative q; it is not an object of A
  fed to the ordinary object-derived functors.
- `TruncationCouple.D F K p q` is literally
  `F.rightDerivedCohomologyWithResolution (truncation K q) r (p + q)`, where r
  is `grothendieckKInjectiveResolutionChoice` for that truncation.
- `TruncationCouple.E F K p q` is the same recorded bridge applied to
  `cohomologyComplex K q`, at degree `p + q`, with its functorial chosen resolution.
  Thus the two displayed term formulas are definitions, not existence predicates
  allowing arbitrary replacement families.
- `transition K q` is the unique chain map from truncLE(q-1) to truncLE(q)
  commuting with the two inclusions into K. `projection K q` is the unique chain
  map to the single cohomology complex whose degree-q component is the cycles
  quotient. Their defining existence/uniqueness claims are separately named
  theorems with complete natural-language proofs in their docstrings.
- `triangle K q` has exactly the three complexes' images under Q as its objects,
  and those canonical first two arrows. `existsUnique_boundary` supplies its
  unique distinguished-triangle connecting arrow. Its docstring explains cone
  comparison, and uniqueness using TR3 and the degree-q cohomology of the third
  term. No arbitrary supplied triangle or arbitrary maps are extra inputs.
- `derivedTriangle F K q` is `F.rightDerivedFunctor.mapTriangle.obj (triangle K q)`.
  This upstream derived functor is computed using K-injectives. `bridgeIso`
  explicitly identifies its cohomology with the chosen-resolution cohomology
  from def-sp-kinjective-bridge: use the resolution quasi-isomorphism, the
  upstream `rightDerivedFunctorObjQIso` at its K-injective target, and
  `DerivedCategory.homologyFunctorFactors`. Consequently this implements the
  specified Rv, rather than introducing a competing derived-functor convention.
- `alpha F K p q` transports the derived image of the truncation inclusion at
  q+1 to `D p q ⟶ D (p-1) (q+1)`. Both total degrees are p+q. The index
  transports are explicit equality morphisms with integer arithmetic proofs.
- `g F K p q` transports cohomology of the second triangle arrow to
  `D p q ⟶ E p q`. Its bidegree is (0,0).
- `f F K p q` transports `DerivedCategory.HomologySequence.δ` of the derived
  triangle from degree p+q to p+q+1, yielding
  `E p q ⟶ D (p+2) (q-1)`. The identity (p+2)+(q-1)=p+q+1 is explicit.
  Hence this is exactly the triangle boundary, not an unspecified map with
  the correct source and target.
- The main definition returns D, E, alpha, f, g in that order. Exactness is not
  required or asserted by this definition: it belongs to the already existing
  separate node lem-sp-truncation-couple-exact. The map types match the recorded
  type-zero `CategoryTheory.BigradedExactCouple` convention. That structure
  additionally contains exactness proofs and hence is deliberately not the
  return type here. No private generic definition of an exact couple is added,
  and no unused ExactCouple import is needed.

Dependency declarations used:

- def-sp-left-exact-additive: Mathlib/CategoryTheory/Preadditive/AdditiveFunctor,
  `CategoryTheory.Functor.Additive`; Mathlib/CategoryTheory/Limits/Preserves/Finite,
  `CategoryTheory.Limits.PreservesFiniteLimits` (available from the bridge import).
  Its record also names `Functor.rightDerived`, whose full signature and
  injective-resolution comparison were read; this construction concerns Rv on
  complexes, so uses the bridge instead of that object-valued functor.
- def-sp-grothendieck-abelian: Mathlib/CategoryTheory/Abelian/GrothendieckCategory/Basic,
  `CategoryTheory.IsGrothendieckAbelian`, at the hom universes as its record requires.
- def-sp-kinjective-bridge: Sheaf.CategoryTheory.KInjectiveBridge,
  `CochainComplex.grothendieckKInjectiveResolutionChoice`,
  `CategoryTheory.Functor.rightDerivedComplexWithResolution`, and
  `CategoryTheory.Functor.rightDerivedCohomologyWithResolution`.
- def-sp-exact-couple: Sheaf.CategoryTheory.ExactCouple,
  `CategoryTheory.BigradedExactCouple` was read to check the three bidegrees;
  it contains exactness and is not needed as data in this definition.
- Existing infrastructure, without new notions: Mathlib cochain smart truncation
  and single complexes; derived-category Q, homologyFunctor, homologyFunctorFactors,
  and HomologySequence.δ; upstream RightDerivedFunctor.KInjective,
  `Functor.rightDerivedFunctorObjQIso`, and RightDerivedFunctor.Triangulated,
  `Functor.rightDerivedFunctor` with its canonical shift and triangle structures.

Four named theorem proofs are `sorry`, as stage 2 requires: `truncLE_plus`,
`existsUnique_transition`, `existsUnique_projection`, and `existsUnique_boundary`.
They are the typing/well-definedness obligations of this definition, carry this
node's blueprint tag, and each has its complete intended proof in its docstring.
All definition data are constructed explicitly; no definition contains sorry.

Edge cases checked: arbitrary integer a, p, q (including q=0 and negative q),
q below the cohomological bound, acyclic and zero K, zero categories, and K with
nonzero terms below a but zero cohomology there. No q>=a restriction or bounded-above
hypothesis is imposed. In a zero/acyclic case the formula still constructs the
same canonical maps; the appropriate derived cohomology objects are zero up to
isomorphism. Universes of the objects and morphisms of A and B are independent.
The boundary and inclusion total-degree arithmetic was checked explicitly.

Searches for an existing definition (real msearch queries in searches.jsonl):

- leanfinder: "truncation exact couple bounded below complex derived functor
  cohomology". Eight results, chiefly `CochainComplex.shortComplexTruncLE` and its
  short-exactness and quasi-isomorphism results. None defines the truncation couple.
- loogle: "truncLE, homologyFunctor". No hits; unknown identifier truncLE.
- leansearch: "truncation couple of a bounded below complex". Service unavailable
  (Internal Server Error), recorded by msearch; no verdict assigned to that service.
- grep of Mathlib: "TruncationCouple|truncation couple". No hits.
- rg over upstream WeilConjectures and lean/Sheaf for
  "truncationCouple|TruncationCouple|def-sp-truncation-couple". No hits before this
  sandbox module; grep/rg of upstream declaration index also returned no such name.
- Further source inspection found upstream unbounded K-injective right derived
  functor and its triangulated and K-injective comparison modules. These are used
  directly, not copied. Searches of Mathlib truncation and single-complex APIs
  located `truncLEXIsoCycles`, `singleFunctor`, and `singleObjXSelf` for canonical
  component specifications.

Validation: scompile.py on the server succeeded cleanly, exit code 0, in 1.8 s;
no errors or warnings. The module declares every universe and variable explicitly.


## Second reading by E1

I read the sandbox module independently against the node and the actual source,
retrieved read-only by ssh from the server: blueprint master,
sec-abelian-varieties/sk-prop-av-pqf-finite/def-sp-truncation-couple.md,
order 520. Its text equals the node statement. This source is a blueprint
MD definition, not a Stacks tag; it has no additional standing hypotheses.
There is no statement_change, new definition node, or dependency module in
this delivery, so the additional H12/H13 and corrected-citer reviews do not
apply. The node has no proof steps, being a definition.

My object/hypothesis/conclusion checklist and verdicts:

1. A and B are Grothendieck abelian categories: the main definition binds
   independent object universes u₁/u₂ and hom universes v₁/v₂, Category,
   Abelian and IsGrothendieckAbelian at each hom universe. PASS. I opened
   def-sp-grothendieck-abelian and Mathlib Basic.lean:55-105: the class at w=v
   expresses AB5 and a separator, with small colimits inferred. No extra
   smallness, finiteness, or field assumption is imposed.
2. v : A -> B, left exact additive: F : A ⥤ B, F.Additive,
   PreservesFiniteLimits F. PASS. I read def-sp-left-exact-additive and the
   definitions in AdditiveFunctor and Limits/Preserves/Finite, the kernel
   comparison in Preadditive/LeftExact, and Functor.rightDerived in
   Abelian/RightDerived. The object-valued rightDerived is not applied to K.
3. K is a bounded-below complex: K : CochainComplex.Plus A. PASS. I opened
   CochainComplexPlus: plus means existence of an integer strict termwise
   lower bound; the node explicitly assumes Ch⁺ in addition to the following
   cohomological bound.
4. Integer a and H^q(K)=0 for q<a: a : ℤ and
   ha : ∀ q : ℤ, q < a → IsZero (K.obj.homology q). PASS. ha does not
   strengthen the bound to termwise vanishing at a. Recording but not using
   this input in the definition is legitimate: the canonical maps exist
   without this bound, and the requested construction accepts it.
5. Smart truncation tau<=q K: truncation K q bundles K.obj.truncLE q.
   PASS. I read CochainComplex/Embedding's truncLE and ιTruncLE definitions
   and truncLEXIsoCycles: degree q is cycles, not a brutal truncation term.
   truncLE_plus is a named proof obligation; no data are sorry.
6. H^q(K)[-q]: cohomologyComplex K q bundles singleFunctor A q applied to
   K.obj.homology q. PASS. For cochain shift convention this has its unique
   supported term in degree q, including negative q.
7. D^{p,q}=H^{p+q}(Rv(tau<=q K)): TruncationCouple.D uses
   rightDerivedCohomologyWithResolution (truncation K q), the recorded
   grothendieckKInjectiveResolutionChoice, and integer degree p+q. PASS.
8. E^{p,q}=H^{p+q}(Rv(H^q(K)[-q])): TruncationCouple.E uses the same
   bridge and resolution convention on cohomologyComplex K q. PASS. I read
   def-sp-kinjective-bridge and all four declarations in its recorded module:
   r.map is a quasi-isomorphism, r.complex is K-injective, RF is the termwise
   image of that complex, and its cohomology is homology at an integer.
9. Maps arise from the canonical truncation triangles after Rv: transition
   is specified by its composite with ιTruncLE; projection is specified by
   its degree-q cycles-to-homology quotient. triangle uses their Q-images
   and the unique distinguished connecting arrow. derivedTriangle uses
   rightDerivedFunctor.mapTriangle. PASS. I read the upstream KInjective
   comparison and Triangulated modules, plus homologyFunctorFactors.
   bridgeIso transports cohomology to the very same chosen-resolution
   objects as clauses 7/8, rather than changing their definition.
10. alpha has bidegree (-1,+1): alpha F K p q maps the truncation inclusion
    at q+1 in degree p+q, then transports to D F K (p-1) (q+1). PASS:
    (p-1)+(q+1)=p+q.
11. f has bidegree (+2,-1) and is the triangle boundary: f uses
    HomologySequence.δ (derivedTriangle F K q) (p+q) (p+q+1) and transports
    to D F K (p+2) (q-1). PASS: (p+2)+(q-1)=p+q+1. I opened the δ
    definition: it applies homology to the third triangle arrow followed
    by the cohomology/shift identification.
12. g has bidegree (0,0): g maps mor₂ of that same derived triangle under
    homologyFunctor B (p+q), transported from D to E. PASS.
13. Pair of bigraded objects with these maps: truncationCouple explicitly
    returns the displayed D, E, alpha, f, g as a dependent pair and triple.
    PASS. I opened def-sp-exact-couple and BigradedExactCouple: its initial
    s=0 map types are exactly these. Its exactness fields are the separate
    lemma lem-sp-truncation-couple-exact, not a missing clause here. A new
    private definition of a generic exact couple would be inappropriate.

I checked the four typing/choice obligations. truncLE_plus follows by choosing
an existing termwise lower bound; the boundary cycles are subobjects of a
zero object if the truncation point lies below that bound. Transition uniqueness
uses the monomorphic inclusion into K. Projection uniqueness uses the fact
that every other target component is zero. Boundary uniqueness is valid here:
TR3 gives an endomorphism of the single cohomology object commuting with the
projection; that projection is an isomorphism on H^q, so the endomorphism has
identity H^q and is itself identity. It therefore identifies the two boundaries.
Thus these are realizable named theorem obligations with complete proof
outlines, not arbitrary morphisms hidden behind existence. Each theorem proof
is sorry, each definition has concrete data, and every declaration has the
source and blueprint docstring. There are no proved theorems in this delivery.

Edge cases: a,p,q range over all integers, including zero and negative indices;
q<a is not excluded. An acyclic or zero K still gives these canonical terms
and arrows, zero up to the expected isomorphisms. Zero abelian categories are
allowed. K may have nonzero terms below a with vanishing cohomology there.
There is no coefficient ring or characteristic restriction, and no scheme
or empty-scheme hypothesis. The index set is ℤ² fixed by the source, so a
separate empty-index-set case is inapplicable. No bounded-above assumption or
extra supplied triangle is required. The main definition installs standard
derived categories, not additional HasDerivedCategory hypotheses.

Independent searches (actual msearch records appended to searches.jsonl):

- leanfinder: "Postnikov filtration cohomological spectral sequence from
  successive intelligent truncations" returned eight smart-truncation
  infrastructure declarations, not this couple.
- loogle: the quoted name substring "truncLE" returned general complex-shape
  and smart-truncation definitions, not a truncation couple.
- grep: "exact.?couple|Postnikov|truncation.?couple" over Mathlib returned
  no matches. The same independent rg over upstream WeilConjectures and
  repository lean/Sheaf found only the general ExactCouple/DerivedCoupleExact
  modules already inspected. These do not construct this truncation couple.
- leansearch: "bigraded cohomology objects obtained by applying a derived
  functor to a Postnikov tower" was unavailable (Internal Server Error);
  no negative verdict is inferred from that service failure.
- rg of the upstream declaration index found no Postnikov/truncationCouple
  declaration. The DAG search found no second node defining this notion.

Mismatches and changes: no mathematical mismatch found; no Lean code or node
statement changed. I replaced the whitespace-normalized lean.statement with
the exact multiline signature from `def truncationCouple` through the return
type, before `:=`, to satisfy literal signature equality, and added this
independent second-reading report. All variables and universes are explicitly
bound. Server scompile.py succeeded, exit 0, 1.8 seconds, no warnings.
