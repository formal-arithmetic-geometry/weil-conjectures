## Worker report

The delivery defines `AlgebraicGeometry.AlgebraicSpace.naiveCotangentComplex` in
`Sheaf.AlgebraicGeometry.SpaceNaiveCotangentComplex`, together with its derived image
`naiveCotangent`, the quotient and differential interfaces, and the Ext convention.
The node's current mathematical statement is preserved. Its existing statement_change
record is retained verbatim. The only changes are its Lean record and addition of the
new definition-node binding `def-sfb-sheaf-polynomial-cotangent-presentation` to
stmt_deps so that Q150’s existing polynomial, ideal and differential constructions
are reused. This repairs H2 in the return on 973fbb1cf6c6. There is no new Lean
dependency module or new mathematical statement correction in this delivery.

Hypothesis and clause correspondence:

- Scheme S, algebraic spaces X and Y over S, and arbitrary morphism f: explicit
  `universe u w`, `variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}` and
  `(f : X ⟶ Y)`. There is no smoothness, flatness, finiteness, nonemptiness, atlas
  choice or representability hypothesis on f.
- The small étale site and its small affine ringed model: every term is in
  `X.SmallModules`, and every chart variable is `X.SmallEtaleModelᵒᵖ`.
  The topology is `X.smallEtaleModelTopology`. These are exactly the existing
  `AlgebraicSpaceSmallRingedModel` constructions, including their induced topology,
  regular-functions ring and restriction equivalence with the original étale site.
- Canonical inverse image, coefficient sheaf A, target sheaf B and structural map:
  `cotangentRingMap f` has domain `(cotangentRingInverse f).obj Y.smallStructureSheaf`
  and codomain `X.smallStructureSheaf`. The imported construction is the
  chart-normalized adjoint mate, transported by the affine-basis equivalences.
  No arbitrary ring map or replacement structure sheaf is an input.
- P=A[B], restriction of coefficients and of generators, and evaluation:
  `cotangentPresentation f` is the existing `SheafPolynomialCotangent.canonical`
  of this precise ring map. Its `generators` is `sets B`, its `values` is the
  identity, and `polynomialSheaf`, `polynomials` and `evaluation` are the existing
  sheafification, coefficient/generator restrictions and evaluation. Thus
  `[b]` evaluates to b. Its `surjective` field is the existing
  `canonical_surjective` proof, justified by the sheafification unit applied to X b.
- I is the evaluation kernel: `SheafPolynomialCotangent.kernelIdeal
  (cotangentPresentation f)` is the already constructed `RingedSiteIdeal`, with
  section ideals literally `RingHom.ker` and its existing module sheaf.
- I² and the sheaf quotient I/I²: `cotangentConormal f` is the real construction
  `SheafOfModules.changeOfRingsOfUniverses evaluation I.module`, namely sheafification
  of B(U) tensor over P(U) with I(U). Since B=P/I as sheaves, this is the canonical
  tensor construction of I/I². This identification is specified, not left implicit:
  `cotangentConormalQuotient` is the actual P-linear map g ↦ 1 tensor g and
  `cotangentConormalQuotient_properties` states its local surjectivity and that
  its kernel consists exactly of sections locally in the square of the kernel ideal.
  The latter is the existing predicate `LocallyInKernelSquare`, using a covering
  sieve and membership in `(RingHom.ker evaluation)^2`, i.e. locally finite sums
  of products of ideal sections. It does not assert that a sheaf quotient is the
  sectionwise quotient on every chart.
- The B action, independence of lifts and restrictions: B acts on the first factor
  of the actual tensor scalar extension. `cotangentConormalClass_relations`
  records addition, `[pg]=evaluation(p) • [g]`, and commutation with restrictions.
  Consequently a lift p of b gives b[g]=[pg]; differences of lifts lie in I and
  products with g lie in I². Changing g by I² has the same result. The quotient
  property and the given B action specify precisely the quotient-module structure
  in the node. There is no existentially chosen module or chosen module instance.
- Ω_{P/A}: the existing `SheafDifferentials.omega (base A (sets B))`, used inside
  `SheafPolynomialCotangent.differentialTerm`, is sheafification of the sectionwise
  Kähler differential presheaf. Its derivation is `SheafDifferentials.derivation`.
  It sends restrictions of p dq to the restrictions of p times d of restricted q.
- Ω tensor_P B: the exact existing `differentialTerm` uses
  `changeOfRingsOfUniverses evaluation omega`. The library's convention places B
  first in this commutative-ring tensor product; the usual tensor symmetry identifies
  it with the displayed Ω tensor_P B. `tensorD P U b p` is the actual sheafification
  unit applied to b tensor dp, not an arbitrary map into a replacement module.
- Differential [g] ↦ dg tensor 1, well-definedness and B-linearity:
  `cotangentDifferential_existsUnique` specifies the unique B-linear sheaf morphism
  whose value on every quotient class is `tensorD P U 1 g`.
  `cotangentDifferential` takes the witness of this exists-unique statement.
  Its docstring gives the complete construction: Leibniz kills I²; its product
  formula with a kernel element makes the factor B-linear; naturality of the
  derivation gives restriction compatibility; the locally surjective quotient gives
  uniqueness. This is permitted selection of a uniquely specified morphism, not
  choice from a bare uncharacterized Nonempty assertion.
- Degrees -1 and 0, zero terms and zero other differentials:
  `naiveCotangentTerm` is the conormal at -1, `differentialTerm` at 0 and the actual
  zero object otherwise. `naiveCotangentBoundary` uses the conormal differential
  exactly in degree -1 and zero elsewhere, with explicit equality transports.
  `naiveCotangentTerm_degrees` and `naiveCotangentBoundary_comp` are the named
  proof obligations used by `CochainComplex.of` in `naiveCotangentComplex`.
- Image in the same D(O_X): `naiveCotangent` is
  `DerivedCategory.Q.obj (naiveCotangentComplex f)` and takes
  `[HasDerivedCategory.{w} X.SmallModules]`. It uses `X.DerivedModules` from the
  recorded derived-module calculus; it neither fixes standard localization size
  nor makes a second derived category.
- Ext for arbitrary E,F and n: `derivedExt X E F n` is exactly `E ⟶ F⟦n⟧` for
  `E F : X.DerivedModules` and `n : ℤ`. `cotangentCoefficient X F` uses the existing
  `DerivedCategory.singleFunctor X.SmallModules 0` to put a sheaf in degree zero.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its Hom;
  `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  its étale charts and regular-functions/module structures.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel`: `SmallEtaleModel`,
  `smallEtaleModelTopology`, `smallStructureSheaf`, `smallStructureRings`,
  `SmallModules` and `smallModuleEquivalence`.
- `Sheaf.AlgebraicGeometry.SpaceCotangentRingMap`: `cotangentRingInverse` and
  `cotangentRingMap`, with the normalization and restriction equivalences read in full.
  This realizes the canonical ringed-topos morphism dependency; no new
  `CategoryTheory.RingedToposMorphism` is constructed or chosen here.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`: `DerivedModules`;
  `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory` and `DerivedCategory.Q`.
- `Sheaf.CategoryTheory.SheafPolynomialCotangentComparison`:
  `canonical`, `polynomials`, `polynomialSheaf`, `evaluation`, `kernelIdeal`,
  `LocallyInKernelSquare`, `differentialTerm` and `tensorD` in namespace
  `CategoryTheory.SheafPolynomialCotangent`. Only the constructions are used;
  no comparison theorem or choice of its `Comparison.models` is used.
- `Sheaf.Paper.RingedSiteIdeal`: `RingedSiteIdeal.module`;
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` and its public
  tensor API: `changeOfRingsOfUniverses`, `changeOfRingsPresheafOfUniverses`;
  `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`:
  `PresheafOfModules.sheafificationAdjunction` and its unit.
- The reused polynomial construction uses `MvPolynomial` and `eval₂Hom`, and
  `CategoryTheory.presheafToSheaf`/`sheafificationAdjunction`; the reused differential
  construction uses `KaehlerDifferential`, its universal derivation and module
  sheafification. Their signatures and documentation were read in Mathlib, together
  with `SheafDifferentials.omega` and `derivation` in
  `Sheaf.CategoryTheory.Sites.InverseImageDifferentials`.

The explicit universe convention uses ring and module sections in u throughout and
allows arbitrary localization morphism universe w. The definition-node binding cites only existing definition nodes and introduces
no comparison theorem dependency or cycle.

Edge cases checked before implementation: empty spaces and empty charts introduce no
nonempty assumption; zero section rings and zero coefficient modules remain allowed;
identity morphisms and arbitrary non-flat morphisms are included; sections of the
sheafified polynomial algebra need not all be polynomials globally, so kernel-square
membership and quotient surjectivity are local. There is no characteristic restriction.
Ext degree zero and negative degrees use the same unrestricted integer shift. Actual
zero terms occur in all complex degrees outside {-1,0}.

Searches performed with prescribed msearch.py: LeanFinder, query “Naive cotangent
complex of sheaves of rings polynomial algebra kernel conormal differentials”, gave
8 ring-level extension/cotangent hits, no algebraic-space or sheaf complex;
Loogle “Algebra.Extension.cotangentComplex, Generators.self” gave no hits and reported
the unqualified Generators.self unknown; Mathlib grep
`naive.*[Cc]otangent|NaiveCotangent|cotangentComplex` returned ring-level cotangent
constructions; LeanSearch “naive cotangent complex sheaves rings conormal” gave
8 ring-level ideal/extension hits. Repository rg for naive/cotangent names found the
landed `SheafPolynomialCotangentComparison` constructions, which are reused, and
ring/topological cotangent comparison modules, which do not define this algebraic-space
complex. rg of WeilConjectures for this node id found no binding. Name-collision searches
in Mathlib, WeilConjectures and Sheaf found no existing declarations at the delivered
full names. The canonical ring-map and small-model dependency source was read locally.

Source checked directly: spaces-more-morphisms.tex, definition-netherlander (0D0V),
and sites-modules.tex, canonical presentation and definition-naive-cotangent-complex
(08TW), plus definition-cotangent-complex-morphism-ringed-topoi (08U0).

All five theorems are left with `sorry`, with source and full natural-language proofs:
`cotangentConormalClass_relations`, `cotangentConormalQuotient_properties`,
`cotangentDifferential_existsUnique`, `naiveCotangentTerm_degrees`, and
`naiveCotangentBoundary_comp` (five theorem declarations in total). They are the
quotient, restriction, well-definedness and complex-law clauses already in this node,
not independent unstated mathematical assumptions. Every definition has real data.
No statement dispute was found.

Validation: scompile.py passed sandbox and library-module compiles, with no errors or
unexpected warnings (16.4 s and 9.3 s in the final explicit compile).

## Second reading by Q62

Author's separate rereading against the current node and all delivered declarations;
the maintainer supplies the independent review. I checked each clause above against
the node and actual source, including the original universe requirement and canonical
ring inverse image, and found no missing hypothesis or weaker object. The key quotient
check is local, not a false assertion that global polynomial evaluation is represented
by a globally polynomial lift: the sheaf quotient is recognized by local surjectivity
and precisely the locally generated square kernel. The tensor construction's B action
is fixed on explicit quotient classes. The only chosen datum is the uniquely normalized
linear differential; no model or arbitrary complex is selected from an existence theorem.
The degree branches are at -1 and 0, the sole boundary starts at -1, and localization
uses the caller's HasDerivedCategory at arbitrary w. The added generic polynomial definition-node
citation does not introduce a dependency cycle. The Ext definition quantifies over all
E,F and all integer n, and the coefficient embedding is degree zero.

Compiler-guided repairs during this rereading: specify the restricted-scalar target of
the quotient's sectionwise linear maps so their P-module action is the evaluation action;
reverse the restriction equality to match PresheafOfModules naturality; open the standard
ZeroObject scope so zero complex terms use the categorical zero object. These repairs
only made the intended interfaces explicit and changed none of the mathematics.


## New nodes

`def-sfb-sheaf-polynomial-cotangent-presentation` owns the existing generic
polynomial-presentation constructions in
`Sheaf.CategoryTheory.SheafPolynomialCotangentComparison`, through `existing: true`.
This is the option explicitly permitted by the return. It binds the definitions
`sets`, `polynomials`, `polynomialSheaf`, `coefficientMap`, `base`,
`evaluationPresheaf`, `evaluation`, `Presentation`, `canonical`,
`LocallyInKernelSquare`, `kernelIdeal`, `differentialTerm` and `tensorD`, and their
existing named proof obligations `canonical_surjective` and `kernel_ideal_axioms`.
Its main signature is the existing `canonical` signature verbatim. No new module,
comparison theorem or `Comparison` data is introduced. The item now cites this
new definition node instead of `lem-sfb-sheaf-polynomial-cotangent-comparison`.
The public import remains the module containing these exact existing definitions.

The source is sites-modules.tex, the polynomial-sheaf and canonical presentation
preceding Tag 08TW and the general generator presentation preceding Tag 08TY.
The small site and same-universe ring and set sheaves are exactly the binders
`{C : Type u} [SmallCategory C] {J : GrothendieckTopology C}`. `polynomials`
implements the coefficient and generator restrictions; `polynomialSheaf` applies
`presheafToSheaf`; `base` is the coefficient inclusion after the sheafification
unit. `evaluationPresheaf` is `MvPolynomial.eval₂Hom`, and `evaluation` is its
adjoint extension. `Presentation` records precisely a generating sheaf, its values
and locally-surjective evaluation. `canonical` uses the underlying set sheaf of B
and identity values. `kernelIdeal` has exactly the evaluation kernels as sections,
and `LocallyInKernelSquare` quantifies over a covering sieve and the square of
those kernels. `differentialTerm` is the actual change of rings of
`SheafDifferentials.omega (base A E)`; `tensorD` applies the module-sheafification
unit to b tensor dp. Thus each clause of the new node is an existing construction.
Empty sites, empty generator sets, zero rings and non-sectionwise-surjective general
presentations are allowed. The canonical presentation has all target sections as
variables; neither surjectivity of the generator map nor global polynomial lifts
for a general presentation are assumed.

The new node records the fresh LeanSearch, LeanFinder and Mathlib grep queries and
results from searches.jsonl. LeanSearch gave eight ring/module-level hits including
`KaehlerDifferential.ideal`, `Algebra.Extension.cotangentEquiv` and module
presentations. LeanFinder gave eight module-presentation and presheaf-differential
hits. Mathlib grep for `SheafPolynomialCotangent|polynomialSheaf|evaluationPresheaf`
gave zero hits. Local rg of WeilConjectures found no such construction; rg of Sheaf
found Q150’s exact definitions and Q107’s duplicate in this item. Searching
`dag/nodes` definition nodes for sheaf polynomial/polynomial sheaf/polynomial
presentation found no generic owner of these constructions (the present algebraic
space node is the consumer). `tools/blueprint_refs.py search 'sheaf polynomial'`
returned zero blueprint matches. The bindings and signatures were read directly.
The existing `def-sfb-sheaf-differentials` is cited for omega and its derivation,
without importing their inverse-image comparison theorem as a DAG dependency.

## Supersession of Q107’s reviewed binding (H4)

This re-delivery deliberately supersedes Q107’s landed, independently reviewed binding
of this item: faa2 PASS, merged 2026-10-24 02:05 UTC. The read-only current main source
and node still have Q107’s `CategoryTheory.SiteNaiveCotangent` implementation. The
returned Q62 packet at 973fbb1cf6c6 already replaced it; the missing explanation was
a report fault. H4 is the reason for the replacement: Q107’s polynomial sheaf,
coefficient/evaluation, kernel and differential constructions duplicate Q150’s
landed `CategoryTheory.SheafPolynomialCotangent` constructions. The replacement
reuses those canonical constructions and keeps the independently checked quotient,
differential, degree, derived-category and Ext semantics. The node’s statement,
source and existing Q107 `statement_change` and nine-citer audit are unchanged.
`AlgebraicGeometry.AlgebraicSpace.naiveCotangentComplex` remains the main name.
The derived image, Ext and degree-zero embedding are now `naiveCotangent`,
`derivedExt` and `cotangentCoefficient` in that same namespace.

Removed declarations, exactly the old main binding minus the retained main name:

- `CategoryTheory.SiteNaiveCotangent.polynomialMap`
- `CategoryTheory.SiteNaiveCotangent.polynomialMap_id`
- `CategoryTheory.SiteNaiveCotangent.polynomialMap_comp`
- `CategoryTheory.SiteNaiveCotangent.polynomialPresheaf`
- `CategoryTheory.SiteNaiveCotangent.polynomialSheaf`
- `CategoryTheory.SiteNaiveCotangent.coefficientApp`
- `CategoryTheory.SiteNaiveCotangent.coefficientApp_naturality`
- `CategoryTheory.SiteNaiveCotangent.coefficients`
- `CategoryTheory.SiteNaiveCotangent.evaluationApp`
- `CategoryTheory.SiteNaiveCotangent.evaluationApp_naturality`
- `CategoryTheory.SiteNaiveCotangent.evaluationPresheaf`
- `CategoryTheory.SiteNaiveCotangent.evaluation`
- `CategoryTheory.SiteNaiveCotangent.evaluation_properties`
- `CategoryTheory.SiteNaiveCotangent.kernel_local_mem`
- `CategoryTheory.SiteNaiveCotangent.kernel_restriction`
- `CategoryTheory.SiteNaiveCotangent.kernelIdeal`
- `CategoryTheory.SiteNaiveCotangent.sectionExtension`
- `CategoryTheory.SiteNaiveCotangent.conormalObj`
- `CategoryTheory.SiteNaiveCotangent.conormalMap_existsUnique`
- `CategoryTheory.SiteNaiveCotangent.conormalMap`
- `CategoryTheory.SiteNaiveCotangent.conormalMap_id`
- `CategoryTheory.SiteNaiveCotangent.conormalMap_comp`
- `CategoryTheory.SiteNaiveCotangent.conormalPresheaf`
- `CategoryTheory.SiteNaiveCotangent.conormal`
- `CategoryTheory.SiteNaiveCotangent.kernelClass`
- `CategoryTheory.SiteNaiveCotangent.differentials`
- `CategoryTheory.SiteNaiveCotangent.differentialSection`
- `CategoryTheory.SiteNaiveCotangent.differential_existsUnique`
- `CategoryTheory.SiteNaiveCotangent.differential`
- `CategoryTheory.SiteNaiveCotangent.term`
- `CategoryTheory.SiteNaiveCotangent.term_degrees`
- `CategoryTheory.SiteNaiveCotangent.boundary`
- `CategoryTheory.SiteNaiveCotangent.boundary_comp`
- `CategoryTheory.SiteNaiveCotangent.complex`
- `AlgebraicGeometry.AlgebraicSpace.naiveCotangentDerived`
- `AlgebraicGeometry.AlgebraicSpace.naiveCotangentExt`
- `AlgebraicGeometry.AlgebraicSpace.naiveCotangentModuleObject`

Importer/citer audit on current main: rg across `lean/Sheaf` and
`lean/WeilConjectures`, excluding the file being replaced, found no occurrence of
`SiteNaiveCotangent`, `naiveCotangentDerived`, `naiveCotangentExt`,
`naiveCotangentModuleObject`, or `SpaceNaiveCotangentComplex`. No other library
module imports the replaced module or uses any removed declaration. The DAG search
likewise found no use of these names outside the item’s own old Lean record. The
nine mathematical citers listed in the preserved statement_change remain valid;
none has a Lean importer or declaration reference to the removed interface. No
consumer requires editing. The only changed fields versus the read-only current
main node are `lean` and addition of the new definition node to `stmt_deps`.

## Repair self-check by Q62

Reopened the returned packet, current main node and module, and the existing
SheafPolynomialCotangent definitions. H2 is repaired by a separate definition-node
ownership record, without a mathematical theorem edge. The new definition node’s
statement was checked clause by clause against all fifteen recorded declarations
as detailed above; its dependencies are the definitions actually used. The existing
module contains the real sheafification and tensor constructions, so the ownership
binding introduces no hollow data. The polynomial comparison theorem and its
`Comparison` record are not used by the item. The supersession section supplies the
H4 rationale, the complete removed-declaration list and the fresh no-users audit.
The substance of the item’s Lean file remains the one independently checked correct
in the return. No theorem proof or mathematical statement was changed in this repair.

Repair validation: explicit scompile.py passed both sandbox and library-name compiles
(16.4 s and 9.3 s), without errors or warnings. The new definition dependency audit
visited 123 nodes with no path back to this item. Machine comparison with current
main confirms only lean and stmt_deps differ, exactly one new definition dependency
is added, and the prior statement_change is byte-for-byte equal as parsed JSON.
The fresh complete declaration/importer audit confirms zero external users of all
37 removed declarations.
