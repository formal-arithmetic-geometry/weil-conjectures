## Worker report

The module `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits` adds
`CategoryTheory.IsSequentialHomotopyColimit`. This item is a composite definition:
all its other notions already have canonical declarations. They are reused through
public imports, not redefined or bundled into an artificial structure. The module
documentation identifies their expressions. No new nodes, dependency modules,
statement correction, or new theorem proofs are delivered.

Clause-by-clause correspondence:

- An abelian category is `[Category.{v} A] [Abelian A]` (Mathlib.CategoryTheory.Abelian.Basic,
  `CategoryTheory.Abelian`). Its complexes and differentials are `CochainComplex A ℤ`,
  `K.X i`, `K.d i j`, with the square-zero condition in `HomologicalComplex`.
  `DerivedCategory A` and `[HasDerivedCategory.{w} A]` are the recorded notions in
  Mathlib.Algebra.Homology.DerivedCategory.Basic. Mathlib's cochain shift has the
  stated positive-degree and negative-differential convention.
- In the etale specialization use `T.smallEtaleTopology` and
  `Sheaf T.smallEtaleTopology AddCommGrpCat.{u+1}`. For a commutative coefficient ring
  use `SheafOfModules ((constantSheaf T.smallEtaleTopology RingCat).obj (RingCat.of R))`,
  with universes as in def-weil-pbc-etale-sheaves. Nothing restricts the general
  abelian-category truncation constructions to these examples.
- For every integer `n`, the two stupid truncations are
  `K.stupidTrunc (ComplexShape.embeddingUpIntGE n)` and
  `K.stupidTrunc (ComplexShape.embeddingUpIntLE n)`. The definition is literally
  restriction followed by extension by zero (Mathlib.Algebra.Homology.Embedding.StupidTrunc,
  `HomologicalComplex.stupidTrunc`). `stupidTruncXIso` identifies retained terms;
  `isZero_stupidTrunc_X` identifies discarded terms. Restriction and extension
  keep precisely internal differentials. The GE version is the subcomplex and
  the LE version the quotient, with no claim of descent to the derived category.
- Good truncations use `K.truncLE n`, `K.truncGE n` from
  Mathlib.Algebra.Homology.Embedding.CochainComplex. `truncLEXIso` and `truncGEXIso`
  identify the strict interior terms. `truncLEXIsoCycles` identifies the degree-n
  kernel, and `truncGEXIsoOpcycles` the degree-n cokernel. The underlying
  HomologicalComplex.truncLE/truncGE constructions induce the boundary
  differentials by the kernel/cokernel universal properties; `truncLEMap` and
  `truncGEMap` give morphisms. `quasiIsoAt_ιTruncLE` and `quasiIsoAt_πTruncGE`
  give retention of cohomology; the strictly-supported instances give zero
  cohomology in the discarded range. Mathlib.Algebra.Homology.DerivedCategory.TStructure,
  `DerivedCategory.TStructure.t`, is the recorded standard t-structure.
- The successive triangle is the recorded `DerivedCategory.truncation_triangle`
  in Sheaf.CategoryTheory.TruncationTriangle. Its third object is
  `Q.obj ((CochainComplex.singleFunctor A n).obj (K.homology n))`, exactly
  H^n(K)[-n]. The cochain representative and localization lift in that theorem
  give the triangle for arbitrary derived objects. There is no new triangle choice.
- The bounded-below, left exact additive, Grothendieck abelian hypotheses are
  precisely those of `CategoryTheory.truncationCouple` in
  Sheaf.CategoryTheory.TruncationCouple: `CochainComplex.Plus A`,
  `[IsGrothendieckAbelian A]`, `[IsGrothendieckAbelian B]`, `[F.Additive]`,
  `[PreservesFiniteLimits F]`, and its lower cohomological bound. Its D/E terms
  and alpha/f/g maps apply the derived functor and cohomology to these triangles.
  The cartesian-square application reuses `AlgebraicGeometry.Etale.hypercohomologyFiltrations`
  and `hypercohomologyFiltrations_spec` in Sheaf.AlgebraicGeometry.HypercohomologyFiltrations.
  A triangle is not identified with a bigraded exact couple.
- In the new predicate the triangulated hypotheses are `[Preadditive C]`,
  `[HasZeroObject C]`, `[HasShift C ℤ]`, additive shifts, `[Pretriangulated C]`,
  `[IsTriangulated C]`, the recorded Mathlib.CategoryTheory.Triangulated notion.
  `[HasCountableCoproducts C]` is precisely the required countable sums.
  `E : ℕ → C` and `u : ∀ j, E j ⟶ E (j+1)` specify exactly the given sequence.
  `∐ E` is the discrete-diagram colimit from Mathlib.CategoryTheory.Limits.Shapes.Products.
  The endomorphism `Sigma.desc (fun j ↦ u j ≫ Sigma.ι E (j+1))` is s, since
  composing with the jth coprojection gives the indicated component.
  `𝟙 (∐ E) - ...` is 1-s. The existential arrows g and h and membership of
  `Triangle.mk ... g h` in `distTriang C` say exactly that H is a cone object
  in the telescope triangle. No object is chosen from mere existence and no
  functorial cone choice is asserted.
- For a small category I and F : I ⥤ Sheaf J AddCommGrpCat, use the existing
  expression `(presheafToSheaf J AddCommGrpCat).obj
  (colimit (F ⋙ sheafToPresheaf J AddCommGrpCat))`. Functor-category colimits are
  objectwise. The sheafification adjunction identifies this with the sheaf
  colimit. The recorded `colimit` is the ordinary category-theoretic colimit;
  `presheafToSheaf`, `toSheafify`, `sheafificationAdjunction` are those in
  Mathlib.CategoryTheory.Sites.Sheafification. The imported
  `CategoryTheory.Sheaf.hasExactColimitsOfShape` in
  Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf gives the recorded
  filtered exactness infrastructure.
- For module presheaves and induced R-actions use the recorded
  `CategoryTheory.moduleSheaves_colimits_forgetful` from
  Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful. Its last conjunct
  specifies module sheafification of `PresheafOfModules.colimitPresheafOfModules`;
  its preservation conjunct identifies the underlying abelian colimit. Its
  hypotheses are those of that dependency, not new hypotheses on the present item.
- The neighbourhood category is `(Scheme.pointSmallEtale s).fiber.Elements`,
  using `CategoryTheory.Functor.Elements` / `categoryOfElements` in
  Mathlib.CategoryTheory.Elements. In Mathlib.AlgebraicGeometry.Sites.EtalePoint,
  `pointSmallEtale` has fiber `Etale.forget T ⋙ coyoneda.obj (op (Over.mk s))`,
  giving exactly pointed lifts and maps preserving them. Its cofiltered
  instance is the anonymous instance recorded by the dependency, hence the
  opposite is filtered. An algebraically closed field satisfies `IsSepClosed`.
- The stalk is `((Scheme.pointSmallEtale s).sheafFiber).obj F` from
  Mathlib.CategoryTheory.Sites.Point.Basic, defined by the presheaf fiber colimit
  over the opposite category of elements. The recorded
  `AlgebraicGeometry.Scheme.geometricStalk_preservesColimits` in
  Sheaf.AlgebraicGeometry.GeometricStalkColimits states both sheaf and
  termwise-complex preservation (integer-module encoding of abelian groups).
  The module-sheaf case uses the preceding preservation-by-forgetting result,
  with its induced coefficient action. No colimit in the derived category is
  substituted for a termwise colimit.

Read the node, every statement-dependency statement and recorded declaration,
Mathlib truncation definitions and standard t-structure, and the existing
TruncationTriangle, TruncationCouple, HypercohomologyFiltrations,
ModuleSheavesColimitsForgetful and GeometricStalkColimits modules. The upstream
EtaleSheaves module is not in the older local source snapshot; a server dependency
probe confirmed that its recorded import and all five Sheaf imports are available.
The specialized predicates of EtaleSheaves are not used here; the category of
sheaves and SheafOfModules are the existing Mathlib definitions specified by its record.

Edge cases checked: n is any integer, including zero and negative values;
truncation at n retains its boundary kernel/cokernel, not the original term;
zero complexes and sheaves are included; empty diagrams give the zero sheaf
through presheaf colimit and sheafification; a zero sequential system gives the
triangle of the zero map between zero objects. The sequence has no lower-bound
or compactness assumption. The predicate does not identify all cones literally,
and does not assert a functor. Object and morphism universes are explicitly
bound and independent; the only coproduct index is the countable type ℕ.
No statement dispute or correction was needed.

Searches performed:

- msearch.py leanfinder: "Stupid and canonical truncations of cochain complexes and
  sequential homotopy colimits given by the cone of identity minus shift".
  Eight hits, including CochainComplex.shortComplexTruncLEX₃ToTruncGE,
  πTruncGE, ιTruncLE and shortComplexTruncLE; no general sequential-hocolimit definition.
- msearch.py loogle: "HomologicalComplex.stupidTrunc, CochainComplex.truncLE,
  CochainComplex.truncGE". Zero hits.
- msearch.py leansearch: "Homotopy colimit of a sequence in a triangulated category
  as a distinguished triangle of identity minus shift". Service unavailable:
  Internal Server Error; no mathematical verdict inferred from this.
- msearch.py grep: `hocolim|homotopyColimit|HomotopyColimit|homotopy colimit`,
  Mathlib/CategoryTheory. Zero hits.
- rg for the same expression in the source WeilConjectures, Mathlib/CategoryTheory,
  and project lean/Sheaf: project telescope lemmas and compact-hom results only.
  Read TelescopeColimit and CompactHomHocolim: the former has a concrete
  sheaf-module-complex 1-shift map, the latter expresses a telescope triangle
  inline; neither defines the general predicate. No duplicate definition added.
- rg for def-kun-truncations in the source WeilConjectures: no hits.

Validation: dependency-import probe and delivered module each compiled cleanly by
scompile.py on the server, nice 19, two threads, 60 seconds per file. The delivered
module took 1.6 seconds, with no errors or warnings. Delivery dry run follows.

## Second reading by ND

Read the blueprint source at sec-smooth-purity/sk-prop-sf-kunneth-ordinary/
def-kun-truncations.md, the current expanded node, all seventeen statement
Dependency records, the delivered module, and the defining source declarations.
The source is a blueprint definition rather than a Stacks lemma; it imposes no
Noetherian, finiteness, characteristic, or boundedness hypothesis on the telescope.
The node already distinguishes the individual triangle from the exact couple;
this delivery contains no statement correction and no new or dependency nodes.

Independent object/hypothesis/clause checklist (each verdict: matches):

1. An arbitrary abelian category and integer-indexed square-zero cochain complex:
   `CategoryTheory.Abelian`, `CochainComplex A ℤ`, `K.X`, and `K.d`, supplied by
   the existing Mathlib imports. `DerivedCategory A` and `HasDerivedCategory`
   are the dependency's localization, with its chosen morphism universe. The
   cochain shift uses degree i+1 and the negative differential as required.
2. The optional etale examples: `T.smallEtaleTopology`,
   `Sheaf T.smallEtaleTopology AddCommGrpCat`, and `SheafOfModules` over
   `(constantSheaf T.smallEtaleTopology RingCat).obj (RingCat.of R)`.
   These are the existing notions in the etale-sheaves dependency record;
   no alternate module category or torsion condition is introduced here.
3. Stupid truncations at every integer n: `K.stupidTrunc
   (ComplexShape.embeddingUpIntGE n)` and the LE counterpart. I read
   `HomologicalComplex.stupidTrunc`: restriction followed by extension by zero.
   `stupidTruncXIso` and `isZero_stupidTrunc_X` give exactly the retained and
   discarded objects, with retained internal differentials. GE is the subcomplex
   direction, LE the quotient direction. No derived stupid truncation is asserted.
4. Canonical truncations: `K.truncLE n` and `K.truncGE n`.
   I checked `truncLEXIsoCycles` and `truncGEXIsoOpcycles`: at n the objects
   are cycles (kernel of the outgoing differential) and opcycles (cokernel of
   the incoming differential), respectively. The strict-interior isomorphisms
   are `truncLEXIso` and `truncGEXIso`; `truncLEMap` and `truncGEMap` give the
   induced morphisms. The quasi-isomorphism-at-degree instances and supported
   ranges give exactly retained cohomology and vanishing outside it.
   `DerivedCategory.TStructure.t` is defined by bounded representatives, with
   `isLE_iff`/`isGE_iff` giving the equivalent cohomology formulation.
5. Successive triangle for K in the derived category:
   `DerivedCategory.truncation_triangle` has the two localized truncations,
   the localized single complex in degree n with object `K.homology n`, and
   the distinguished-triangle condition. Its localization-lift clause covers
   morphisms between representatives; every derived object has a representative.
   The single object is precisely H^n(K)[-n], with the stated shift convention.
6. Bounded-below derived exact-couple application:
   `CategoryTheory.truncationCouple` takes `CochainComplex.Plus A`, the lower
   cohomological bound, Grothendieck abelian A/B, additive F preserving finite
   limits. I read its D/E, alpha, f and g constructions: they apply the derived
   functor and cohomology to these same triangles. The cartesian-square
   application is the imported `Etale.hypercohomologyFiltrations` and its spec;
   its hypotheses remain those of that dependency, as the node requires.
7. Arbitrary triangulated category with countable coproducts:
   the new predicate binds `{C : Type u} [Category.{v} C]`, preadditivity,
   zero object, integer shifts and additive shifts, `Pretriangulated C`,
   `IsTriangulated C`, and `HasCountableCoproducts C`. Reading the Mathlib
   class signatures confirms these are exactly the triangulated structure
   and countable sums, with no additional compactness or geometric condition.
8. Given sequence and coproduct: `(E : ℕ → C)` and
   `(u : ∀ j : ℕ, E j ⟶ E (j + 1))`; `∐ E` is the discrete-diagram colimit,
   and `Sigma.ι E j` its coprojection. No extra compatibility data is needed
   for a sequence, whose composites are determined by its successor maps.
9. Successor and telescope: `Sigma.desc (fun j ↦ u j ≫ Sigma.ι E (j + 1))`.
   The source signature of `Sigma.desc` and `Sigma.ι_comp_desc` verify the
   jth component is precisely u_j followed by the next coprojection. Thus
   subtracting this from `𝟙 (∐ E)` is exactly 1-s, in the correct direction.
10. Cone object H: `(H : C)` followed by existential g and h and
    `Triangle.mk (1-s) g h ∈ distTriang C` gives exactly the definition.
    There is no canonical-cone choice, functor, uniqueness equality, or
    additional conclusion. The definition's data is an explicit proposition;
    it contains no sorry and introduces no proof obligation or axiom.
11. Every small sheaf diagram: the module documents the existing expression
    `(presheafToSheaf J AddCommGrpCat).obj
    (colimit (F ⋙ sheafToPresheaf J AddCommGrpCat))`.
    I read `presheafToSheaf` and `sheafificationAdjunction`: this is the
    sheafification of the objectwise presheaf colimit, hence the sheaf colimit.
    The module-sheaf dependency explicitly quantifies over small categories,
    supplies module-presheaf sheafification and the canonical coprojections,
    and states preservation by forgetting to abelian sheaves.
12. Geometric point and pointed neighbourhoods: `pointSmallEtale s` has fiber
    `Etale.forget T ⋙ coyoneda.obj (op (Over.mk s))`. Its Elements objects
    are exactly lifts and its morphisms preserve the lifts. The source has
    the cofiltered instance; the opposite is therefore the filtered index.
    Algebraically closed fields satisfy the required `IsSepClosed` instance.
13. Stalk and colimit commutation: `Point.presheafFiber` is whiskering by the
    opposite Elements projection followed by `colim`; `sheafFiber` restricts
    it to sheaves. I read `Scheme.geometricStalk_preservesColimits`: it states
    preservation both for sheaves (integer modules encode abelian groups)
    and for `mapHomologicalComplex (ComplexShape.up ℤ)`. For abelian sheaves
    at other value universes the same Mathlib point/skyscraper adjunction
    gives preservation directly. Module coefficients are carried through the
    imported forgetful preservation result. These are termwise complex
    colimits, never derived-category colimits.

Edge cases: n ranges over all integers, including zero and negative integers;
zero complexes retain the zero kernel/cokernel at the boundary. The zero
sequential system is included. ℕ is the prescribed sequence index, so an empty
sequence index is not an omitted case. The separate arbitrary-small-diagram
clause includes empty diagrams and gives the zero sheaf. Empty schemes are
allowed; their lack of geometric points makes the stalk assertion vacuous,
not the sheaf-colimit construction. No characteristic restriction occurs.
The telescope object's universe u and morphism universe v are independently
bound; its index is genuinely countable. No unbound implicit variable or
universe occurs in the delivered signature, and the node's `lean.statement`
is verbatim the signature before `:=`.

Independent H4 searches used different wording from the author:

- LeanFinder: "Mapping telescope in an additive category: cone object of one
  minus successor on a countable coproduct". Eight hits concerning sequential
  products and `Functor.OfSequence.map`; none defines the telescope predicate.
- Loogle: `CategoryTheory.Limits.Sigma.desc`. Twelve hits confirm the universal
  coproduct map and its component equation; no homotopy-colimit predicate.
- rg: `telescope|[Hh]ocolim|[Hh]omotopy[Cc]olimit|homotopy colimit` in Mathlib's
  CategoryTheory, source WeilConjectures, and project lean/Sheaf. I opened
  `CochainComplex.telescopeShift` in Algebra/Homology/TelescopeColimit and
  `CategoryTheory.compact_hom_hocolim`: the former is a concrete map on
  module-sheaf complexes; the latter assumes the triangle inline with a
  universe-lifted coproduct. Neither defines this general predicate. Existing
  truncation, sheafification and stalk definitions are reused rather than copied.

No mathematical or signature mismatch was found. No Lean or node change was
needed; this independent reading and its searches are the only additions.
There is no theorem proof to audit against proof steps: this is a definition
node with empty `proof`, and the sole new declaration is a real Prop-valued def.
