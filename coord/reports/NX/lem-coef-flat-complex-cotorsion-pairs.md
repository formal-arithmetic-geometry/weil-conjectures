## Worker report

The module `lean/Sheaf/Algebra/Homology/FlatComplexCotorsionPairs.lean` states
`CategoryTheory.CoefficientFlatCotorsion.flat_complex_cotorsion_pairs`.
Its ten auxiliary predicates explicitly unpack the notions introduced in this
node's own statement; they are listed in `lean.declarations`. No other DAG node
is stated. Every definition has an explicit predicate body, and the only `sorry`
is the main named theorem. Its docstring reproduces the node's complete nine-step
natural-language proof, including all cited dependencies.

The previous attempt's missing-declaration failure is resolved in the current
published compiler environment. The same draft now compiles locally through
`scompile.py`; no dependency replacement, universe identification, or copied
K-flat definition was needed. The exact recorded independent-coefficient predicate
is used. The repaired module also imports all currently stated proof dependencies.

Clause-by-clause correspondence:

- An arbitrary site is encoded by `C`, `Category.{v} C`, `J : GrothendieckTopology C`.
  `EssentiallySmall.{r} C` is smallness relative to coefficient/module universe r.
  The object, morphism, and coefficient universes remain separate. The explicit
  HasSheafCompose, WEqualsLocallyBijective and HasSheafify arguments supply standard
  sheafification infrastructure, with no assumption about points or projectives.
- R is `Sheaf J CommRingCat.{r}`. Module sheaves are the recorded `ringedSiteModules`
  applied to the forgotten ring sheaf; complexes use Mathlib `CochainComplex ... ℤ`.
- W is `HomologicalComplex.Acyclic`, and `FlatKFlat` combines flatness of every term
  using `SheafOfModules.IsFlatOnSite` with the recorded independent-coefficient
  K-flat predicate.
- Global Hom is exactly Mathlib `CochainComplex.HomComplex`. Its documented cochains
  are families of global module morphisms in degree r with the signed differential;
  no sheaf internal Hom enters the statement.
- `Orthogonal U V` quantifies over every short exact sequence with endpoints V,U
  and asks for a section of its epimorphism. `IsCotorsion T` tests this predicate
  against every tensor-flat module sheaf.
- `RightClass T` is termwise cotorsion plus global Hom acyclicity from every member
  of D ∩ W. `TrivialRightClass T` uses every member of D instead.
- The theorem's first conjunct is E₀ = E ∩ W, expressed pointwise by an iff.
  Its other conjuncts assert the two complete hereditary small cotorsion pairs.
- `IsPair` contains both orthogonal equalities. `IsComplete` gives both specified
  short exact approximation sequences for every X. `IsHereditary` requires kernel
  closure of the left class under epimorphisms and cokernel closure of the right
  class under monomorphisms. `IsSmall` supplies an index type in universe r and
  monomorphisms with left-class cokernels; Mathlib `HasLiftingProperty` gives
  exactly the square/filler property, equivalent to epic with right-class kernel.
  These are helpers of the notions explicitly introduced in this item's own statement.
- The only sorry is the named theorem, with all nine natural-language proof steps
  from the node in its docstring. Definitions have explicit predicate bodies.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`; the topology formulation retains
  its documented Mathlib GrothendieckTopology/Sheaf component.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex`.
- `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`:
  `HomologicalComplex.Acyclic` (the acyclicity node is a Mathlib leaf).
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`.
- `Sheaf.Algebra.Homology.KFlat`:
  `CochainComplex.IsKFlatIndependentCoefficients` (source and compiled binding checked).

Edge cases inspected: all degrees range over integers, with no boundedness;
zero complexes and the empty site are permitted; the generating set may be empty;
all global Hom cochains include every integer component; ring zero is permitted;
there is no enough-points, enough-projectives, or sectionwise-flatness hypothesis.
No mathematical statement correction or dispute is asserted.

Searches:

- msearch LeanFinder, `flat complexes cotorsion pairs`: eight hits on flat-module
  tensor exactness and K-projective/K-injective complexes, no matching theorem.
- msearch Loogle, `Cotorsion, Flat, KFlat, Complex`: no hits, unknown Cotorsion.
- msearch grep, `cotorsion` in Mathlib: no hits.
- msearch LeanSearch, `complete hereditary small cotorsion pair in category of
  complexes of flat sheaves`: eight hits on Grothendieck complexes, flat tensor
  exactness, HasExt and idempotent completeness, no matching theorem.
- ripgrep of `cotorsion` in project and upstream: only upstream reference citations
  in SerpeCardinal/SerpeGeneratingSet; no cotorsion-pair declarations.
- ripgrep of this item's id in upstream: no hits.
- ripgrep of HomComplex in Mathlib: read `HomComplex.Cochain`, its degree-family
  definition, and `CochainComplex.HomComplex` with its differential construction.
- Searched the DAG for cotorsion and reviewed the current item's six statement
  dependencies and their Lean/mathlib bindings. No matching existing theorem.

Proof-dependency imports, in addition to the statement-dependency imports above:

- `Sheaf.CategoryTheory.RingedSiteGrothendieckAbelian` for
  `SheafOfModules.grothendieckAbelian_with_localized_generator`.
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic` for
  `CategoryTheory.IsGrothendieckAbelian`.
- `Sheaf.Algebra.Homology.KFlatTelescopeClosure` for
  `CochainComplex.kFlat_closure`.
- `Mathlib.Algebra.Homology.BifunctorShift` for `CochainComplex.mapBifunctor`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatQuotientTensorSES` for
  `SheafOfModules.flat_quotient_tensor_shortExact`.
- `Mathlib.Algebra.Homology.HomologySequence` for
  `CategoryTheory.ShortComplex.ShortExact.homology_exact₂` and its connecting maps.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed` for
  `SheafOfModules.tensorClosed`.
- `Sheaf.Algebra.Homology.AcyclicKFlatCyclesFlat` for
  `CochainComplex.isFlat_cycles_of_acyclic_isKFlat`.

The four proof dependencies `lem-coef-module-flat-cotorsion-foundation`,
`lem-coef-hereditary-cotorsion-complex-lift`,
`lem-coef-generating-set-cotorsion-smallness`, and
`lem-coef-exact-flat-complex-set-cogeneration` have no Lean records yet, so there
are no modules to import for them. They are cited in the proof docstring.
There is no import cycle.

Additional checks on this repair: Mathlib's `EssentiallySmall.{r}` is explicitly
an equivalence to a category small in universe r (both objects and morphisms).
Thus it supplies the intended small-site condition without constraining the
presentation universes u and v. `HomComplex.δ_v` has second coefficient
`(r+1).negOnePow`, exactly minus `r.negOnePow`, giving the stated differential.
`ShortComplex.ShortExact` is exactness together with a mono first map and epi
second map; a section in `Orthogonal` therefore means splitting exactly as stated.
`HasLiftingProperty` quantifies over all commutative squares and supplies a lift.
The empty generating family is allowed by `I : Type r`, with no `Nonempty` binder.
No new nodes, dependency modules, statement changes, or mathematical disputes.

Validation: `scompile.py NX lem-coef-flat-complex-cotorsion-pairs` compiled this
module as an isolated sandbox and as its actual library module, both cleanly.
`deliver2.py NX lem-coef-flat-complex-cotorsion-pairs --no-push` printed
`OK (dry run)`: the commit compiles and passes preflight except for the independent
second-reading section, which the second reader supplies. Nothing was pushed.

## Second reading by NX

I independently read the sandbox node and module, all six statement-dependency
records and their actual declaration sources, and the item's nine proof steps.
No statement mismatch was found. The Lean source and node record are retained
verbatim; this second reading adds only this review report.

Source check: the node explicitly describes an additional agent-formulated
foundation, not a theorem bearing a Stacks tag. I read its actual blueprint
source, `prop-coef-integral-exceptional-adjoint.md`, especially the second proof
paragraph's derived coefficient adjunction. I also read Stacks `sites.tex`,
Definition 00VH and its size clarification; `sites-modules.tex`, Definition
03CV and Definition 03ER(3); and `sites-cohomology.tex`, Section 06YL and
Definition 06YN. These assume a ringed site, with no points, projectives,
Noetherian, characteristic, or boundedness condition.

For the external source named by the node I independently opened
[Recktenwald's thesis](https://d-nb.info/1211326829/34), Definition 2.2.4,
Proposition 2.2.7, Theorem 2.2.13, Theorem 2.5.35, Proposition 2.5.37 and
Corollary 2.5.38. These use arbitrary small ringed sites and the flat/cotorsion
classes; their dg definitions test null homotopy of global chain maps.
Testing all shifts gives the global-Hom acyclicity formulation used here.
As the node already says, the K-flat identification and the specific smallness
conclusion are additional content justified by its detailed proof, rather than
a quotation of a Stacks lemma or of that corollary alone.

The following is my object/hypothesis/conclusion inventory and its Lean match.

1. A small site: `C : Type u`, `[Category.{v} C]`,
   `[EssentiallySmall.{r} C]`, `J : GrothendieckTopology C`.
   Verdict: correct. `SiteCoveringAxioms.IsSiteForCoverings` documents the
   covering-family presentation; its associated Grothendieck topology gives
   the same sheaf category, which is all this statement uses. A topology
   avoids imposing arbitrary pullbacks on the underlying category. The
   essentially-small presentation admits every small site in the coefficient
   universe, without equating object and morphism universes.
2. A sheaf of commutative rings: `R : Sheaf J CommRingCat.{r}`.
   Verdict: correct; this is neither a field nor a constant ring restriction.
   The explicit `HasSheafCompose`, `WEqualsLocallyBijective`, and `HasSheafify`
   arguments are standard infrastructure available on these sites, not
   geometric assumptions. I checked Mathlib's transport in
   `Sites/Equivalence.lean` and the coefficient-universe sheafification and
   locally-bijective instances in the recorded `KFlat.lean`.
3. The abelian category A = Mod(R): every occurrence uses
   `ringedSiteModules.{r} ((sheafCompose J
   (forget₂ CommRingCat.{r} RingCat.{r})).obj R)`.
   Verdict: correct. I opened `RingedSiteModules.lean`: this is transparently
   Mathlib's `SheafOfModules`, with linear natural morphisms and its abelian
   structure. Forgetting a commutative ring to a ring does not change modules.
4. The unbounded cochain category B: `CochainComplex (...) ℤ`.
   Verdict: correct. I read Mathlib's `CochainComplex` abbreviation: its shape
   is `ComplexShape.up ℤ`, so differentials raise degree and square to zero.
   No boundedness, nonnegative-degree, or projectivity restriction occurs.
5. W, the acyclic complexes: `P.Acyclic` and `T.Acyclic`.
   Verdict: correct. The recorded Mathlib declaration is exactness at every
   index, equivalent in these abelian categories to zero cohomology objects.
6. D, flat terms and K-flatness: `FlatKFlat` is the conjunction of
   `∀ n : ℤ, SheafOfModules.IsFlatOnSite (P.X n)` and
   `CochainComplex.IsKFlatIndependentCoefficients P`.
   Verdict: correct. I opened both dependency definitions. `IsFlatOnSite`
   uses exactness of the sheafified sectionwise tensor functor, not flatness
   of all sections. The recorded independent-coefficient K-flat predicate
   tests acyclicity of the direct-sum total tensor against every acyclic
   complex. It does not replace K-flatness by K-projectivity.
7. The global Hom complex and its sign: `CochainComplex.HomComplex P T`.
   Verdict: correct. I read `HomComplex.Cochain`, `δ`, `δ_v` and `HomComplex`
   in Mathlib. A degree-r term is the family of global module morphisms
   indexed by p,q with p+r=q. With target degree r+1, `δ` has coefficient
   `(r+1).negOnePow = -r.negOnePow` on the precomposition term, exactly the
   node's differential. No internal sheaf Hom or section functor is used.
8. Ext-one vanishing means splitting every short exact extension:
   `Orthogonal U V` quantifies over every E,i,p,z with
   `(ShortComplex.mk i p z).ShortExact`, and asks for q with `q ≫ p = 𝟙 U`.
   Verdict: correct orientation for extensions of U by V. I opened
   `ShortComplex.ShortExact`: exactness plus mono i and epi p gives precisely
   the stated sequence. In an abelian category a section of p is splitting.
9. A cotorsion module: `IsCotorsion T` quantifies over every module F with
   `SheafOfModules.IsFlatOnSite F`, and requires `Orthogonal F T`.
   Verdict: exactly the stated flat right orthogonal.
10. E: `RightClass T` requires `∀ n, IsCotorsion (T.X n)` and acyclic global
    Hom from every P satisfying `FlatKFlat P` and `P.Acyclic`.
    Verdict: exactly D intersect W as test class, with the right quantifiers.
11. E₀: `TrivialRightClass T` has the same term condition and tests every P
    satisfying `FlatKFlat P`, without assuming P acyclic.
    Verdict: exactly the larger test class D required by the node.
12. E₀ = E intersect W: the theorem's first conjunct is
    `∀ T, TrivialRightClass T ↔ RightClass T ∧ T.Acyclic`.
    Verdict: the pointwise iff gives equality of these object classes.
13. The two cotorsion pairs: the remaining two conjuncts apply
    `IsCompleteHereditarySmallPair` to `(FlatKFlat, TrivialRightClass)` and to
    `(fun P ↦ FlatKFlat P ∧ P.Acyclic, RightClass)` respectively.
    Verdict: exactly (D,E₀) and (D intersect W,E), in the correct order.
14. Each pair has both orthogonal equalities: `IsPair` contains both
    universally quantified iff statements with `Orthogonal U V`.
    Verdict: neither orthogonal equality is omitted or reversed.
15. Completeness: `IsComplete` gives, for every X, the short exact sequences
    V→U→X and X→V→U with right-class V and left-class U in both cases.
    Verdict: exactly the two approximations; the witnesses are independently
    existentially quantified, as T,L and T',L' are in the node.
16. Heredity: `IsHereditary` requires left-class closure under `kernel p`
    for epis between left-class objects, and right-class closure under
    `cokernel i` for monos between right-class objects.
    Verdict: exactly the node's explicit convention, without an added
    higher-Ext or enough-projectives assumption.
17. Smallness: `IsSmall` provides `I : Type r`, U,V and arrows i indexed by I,
    each mono with left-class cokernel. For every p its displayed iff says
    `∀ j, HasLiftingProperty (i j) p` exactly when p is epi and its kernel is
    in the right class. Verdict: correct. I read Mathlib's class: it tests
    every commutative square and supplies a diagonal with both triangles.
    A set-indexed family can repeat arrows without changing this condition.
    Both pair assertions specialize the generating index universe to r.

Edge cases: an empty site is permitted, as are empty covers and zero modules
and complexes. There is no `Nonempty` constraint on I; the zero category can
use an empty generating family. Degrees include all negative integers and
zero, with no exceptional degree-zero hypothesis. The zero ring and all
characteristics are allowed. No scheme appears, so the empty scheme is
covered through its site rather than by any nonemptiness assumption.
The universes u,v,r remain independent, subject only to the intended
smallness relative to r. Consequently a presentation with different object
and morphism universes is accepted; no equality u=v or r=u is imposed.
Global Hom may live in the larger ambient morphism universe, which is allowed
by Mathlib's `AddCommGrpCat` and acyclicity definitions.

Independent duplicate searches, using vocabulary beyond the first worker's:

- LeanFinder via msearch: `Ext orthogonal classes of unbounded flat sheaf
  complexes with small generating monomorphisms`. Eight hits on HasExt,
  small Ext and derived-category bounds; none defines the cotorsion notions
  or states the theorem.
- Loogle via msearch: `"cotorsion"`. No hits.
- LeanSearch via msearch: `Acyclic K flat complexes and degreewise cotorsion
  complexes form a complete hereditary pair`. Eight hits on acyclicity,
  K-projective orthogonality, Grothendieck complexes and ordinary module
  tensor exactness; none is this theorem.
- msearch grep: `Orthogonal|IsCotorsion|IsCompleteHereditarySmallPair`.
  The returned Mathlib hits are unrelated linear-algebra orthogonality.
- Direct `rg -i 'cotorsion|deconstructib|dg.?flat'` over Mathlib, upstream
  `WeilConjectures` and project `lean/Sheaf` found only bibliographic
  cotorsion mentions in upstream Serpe modules, no reusable declaration.
  DAG searching finds the current statement and its foundations/consumers;
  no independently recorded definition node carries these inline notions.

The ten auxiliary predicates simply unpack notions explicitly introduced in
this node's own statement; they use the recorded dependency definitions and
Mathlib exact sequences, Hom complexes and lifting properties. They have real
predicate bodies. No missing definition node or unusable statement dependency
was found, so no new node or dependency module is needed. The four unstated
proof dependencies are not needed to type the statement and remain proof-plan
citations. Every recorded proof dependency's module is imported.

H5/H6/H8/H9 check: there is exactly one `sorry`, the main named theorem;
no data definition or auxiliary theorem is hollow or newly proved. Each
declaration has its source/blueprint docstring. I compared all nine numbered
docstring steps with the node: module foundation, lifted pairs, both
smallness applications, K-flat factors, transfinite tensor argument, acyclic
kernel, section correction, E/E₀ identification, and final assembly are all
present. There is no local notation, private definition or local instance;
all lines are at most 100 characters and all universes and variables are
bound. The node's `lean.statement` is verbatim the signature before `:= by`.
There is no `statement_change`, and none is needed; no citer audit is triggered.

Validation: the full module compiled with no diagnostics through
`scompile.py NX lem-coef-flat-complex-cotorsion-pairs <absolute module path>`,
both as `Sheaf.Stage2.Sandbox0` and its actual library module, 3.3 seconds
each. An initial relative-path invocation from the read-only checkout could
not find the sandbox file; rerunning with its absolute sandbox path resolved
that invocation error without changing source or tools.

## Maintainer repair of duplicate predicates

Independent immutable review found H4: the landed module
`Sheaf.CategoryTheory.SmallCotorsionModelRecognition` already supplies
`CategoryTheory.Cotorsion.ExtOneOrthogonal`, `IsCotorsionPair`, and `IsComplete`.
The replacement file imports that module, removes `Orthogonal`, `IsPair`, and
`IsComplete`, and uses the shared predicates directly. Its `IsSplitEpi p`
means precisely the existence of a section with section ≫ p = identity, so
all mathematical clauses and quantifier orders are preserved.

The seven remaining helpers have real predicate bodies. The smallness helper
retains an independent index universe s, specialized to coefficient universe r
in the main theorem; the existing `Cotorsion.IsSmall` fixes its index to the
ambient Hom universe, so it is not an exact size match for a large presentation
of an essentially small site. The generalized helper now reuses the shared
`monomorphismsWithCokernel`, `epimorphismsWithKernel`, and Mathlib's right
lifting class. Equality of morphism properties gives exactly the original
pointwise iff for every map, without a change to the smallness claim.
No site-universe equality, new hypothesis, statement correction, or proof is added.
The main signature remains verbatim the recorded signature.

This supersedes the earlier duplicate-search conclusion in both original report
sections: that conclusion missed the existing recognition module. The independent
review's direct search located it, and a read-only git object check confirmed
that the module already existed in immutable commit
`fd2369203d45b3d86835bfd3dd3175a6ee90674a`.

Maintainer validation: the immutable original compiled through `scompile.py`
as `Sheaf.Stage2.Sandbox0` (3.5 s) and its actual library module (3.6 s).
The complete replacement compiled through the same wrapper as
`Sheaf.Stage2.Sandbox0` and `Sheaf.Stage2.Check` (3.1 s each; the latter name
is the wrapper's fallback for a file under fixes/ rather than lean/).
Both runs exited 0 with no diagnostics. The replacement's recorded signature
is verbatim, all lines meet 100 columns, and its sole proof remains `sorry`.
No project clone, immutable delivery file, branch, or live Lean artifact was edited.
