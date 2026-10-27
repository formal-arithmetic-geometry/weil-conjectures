## Worker report

Item: lem-sfb-abelian-space-poincare-calculus. Group NO, 2026-10-24.

The theorem is AlgebraicGeometry.AlgebraicSpace.abelianSpace_poincare_calculus in
Sheaf.AlgebraicGeometry.AbelianSpacePoincareCalculus. The supporting definition module is
Sheaf.AlgebraicGeometry.AbelianSpacePoincareData, namespace
AlgebraicGeometry.AlgebraicSpace.Poincare. This is stage 2: the main theorem and the
terminal-base proof obligation baseMap_eq have sorry proofs. Every definition has real
data. No statement correction or STATEMENT-DISPUTED issue was found.

### Sources read

I read the item and all four original statement-dependency records and their recorded
Lean declarations and docstrings. I read Milne, Abelian Varieties, Chapter I Sections
8--9, especially the universal property and Remarks 8.7 and the opening of Section 9.
I obtained the Numdam primary PDF
https://www.numdam.org/item/AST_1985__127__131_0.pdf in this sandbox and read Deligne's
Section 4.1 on printed pp.141--142: the diagonal pullback of the Poincare module gives
the canonical ample line, with its zero trivialization and base-change compatibility.
This is the relative input implicit in that source, not a claim that Milne's field
result already proves relative algebraic-space representability. The theorem docstring
reproduces all six DAG proof steps with their named prerequisites.

The current blueprint was read in literature/blueprint/latest/blueprint/
sec-six-functors-basics/sk-thm-sf-ctf-stability/:
sk-thm-sf-ctf-stability-direct-images.md and its proof.md. Its direct-image clause is
the ancestor route recorded by the existing split. blueprint_refs.py ancestor reports
None for this inherited node, and the new definition keeps that exact ancestor result
and extends the existing via chain; it changes no unit.

### Hypothesis and clause correspondence

1. A scheme S, locally Noetherian: `(S : Scheme.{u}) [IsLocallyNoetherian S]`.
The source, target and every test field use the same scheme universe u. There is no
extra relation between an independent site and coefficient universe.

2. A commutative group algebraic space: `(A : AlgebraicSpace S)` and
`(g : CommutativeSpaceGroup A)`. This is the already published pointwise natural
group law, not a private replacement. `pointedGroup A g` retains its actual identity
and structural map. `addition A g` is multiplication of g's two projected sections;
multiplicative notation in the implementation is additive notation in the node.

3. Proper smooth finite presentation and abelian geometric fibres:
`hA : IsAbelianFamily (groupSpaceProjection A)`. Unfolding this gives
`MapIsProper`, `MapIsLocally (@Smooth)`, `MapIsLocallyOfFinitePresentation`, and
`HasAbelianFibres`. The existing properness predicate means separated, finite type,
universally closed. Finite type gives quasi-compactness, separatedness gives
quasi-separatedness, so local finite presentation is precisely finite presentation
here. All these are the existing etale-chart definitions, not scheme-only tests.
For every algebraically closed field K and point, HasAbelianFibres supplies a scheme
Z over Spec K, an actual cartesian comparison to A, and upstream IsAbelianVariety Z.
Its group law is inherited through this cartesian comparison from g by Yoneda.
Over an algebraically closed field connected smooth proper group schemes are the
geometrically connected abelian varieties intended by the node.

4. The correct module category: `X.SmallModules` is the published equivalent small
affine model of the small etale site. `IsLine X L` is exactly
`X.IsLineModule (X.smallModuleEquivalence.inverse.obj L)`, the published locally
structure-module condition. `schemeModule` extends through that same fixed equivalence
and restricts on the represented scheme's identity etale chart by schemeRestriction.
Thus fibre algebraic equivalence is the existing ordinary invertible-module relation,
not an abstract predicate on unrelated data. The internal dual is literally
`SheafOfModules.homObj L (unit)`. The monoidal structure is the existing sheaf tensor.

5. Existence and geometry of the dual: the existential D, h, P, r is followed by
`IsAbelianFamily (groupSpaceProjection D)`. Thus D is another commutative group
algebraic space of exactly the same kind, with a module on the actual A x_S D.
There is no scheme-representability or projectivity hypothesis on A or D over S.

6. Universal line for all parameters: `Represents (pointedGroup A g)
(pointedGroup D h) P r`. It asserts IsLine P, fibrewise algebraic triviality over D,
and, for EVERY `(T : Over S)`, every map `schemeSpace T` to the base, every line L
on the actual A_T, and every identity rigidification r, an exists-unique classifying
map. Classifies requires the map to be over the base and an actual isomorphism from
the P pullback to L preserving the specified rigidification through the canonical
pullback composition and unit maps. No local-Noetherian or reduced hypothesis is
imposed on these T. Existence of this normalized isomorphism is the groupoid's
isomorphism-class classification, and its uniqueness follows from the separate
rigid-automorphism assertion. All geometric points are tested, and the exact existing
AreAlgebraicallyEquivalent relation is used: the equivalence closure of isomorphisms
and fibres of lines over smooth connected separated finite-type parameter schemes.

7. Both axis trivializations and their intersection: the existential
`r : Axes ... P` has left and right isomorphisms to the respective structure modules.
Its intersection field compares their restrictions along the two zero sections using
pullbackComp, equality of the two axis composites, and pullbackUnit. Equality of the
axis composites follows from the actual fibre-product maps and the section identities;
the universally quantified equality proof is therefore never a vacuous condition.

8. All rigidified automorphisms, including nontrivial components:
`RigidAutomorphisms (pointedGroup A g)` quantifies over every T, every line L and every
rigidification, and says an isomorphism L to itself whose restricted map fixes r is
Iso.refl L. It contains no FibrewiseTrivial restriction.

9. The two Poincare identities: `Biadditive A D g h P`. Its first clause uses
`pointedProduct A A` with D and the actual map addition A g, versus the two actual
first/third and second/third projection pullbacks tensored together. Its second uses
A with `pointedProduct D D` and addition D h, versus the first/second and first/third
projection pullbacks. CanonicalAxisEquivalent requires the unique axis-preserving
isomorphism and its actual pullback compatibility under every locally Noetherian
base change. On A x A x D the grouped left axis is (0,0,z) and the grouped right
axis is (x,y,0); normalization there determines normalization also on the two
individual addition-zero loci by the same unit/section argument in DAG proof step 3.
The corresponding observation holds for the second identity.

10. The literal difference, with no forgotten constant: `difference A g L` is
`(((m^*L tensor p1^*dual L) tensor p2^*dual L) tensor (p1 >> p_A >> e_A)^*L)`.
The last pullback is canonically q^*e_A^*L by pullbackComp. Thus it is exactly N_L,
including the identity-line factor even when e_A^*L is nontrivial on S.
`DifferenceHomomorphisms` quantifies over every line and supplies phi with IsHom,
`ClassifiesDifference ... psi iff psi = phi` for every psi, and the base-change
compatible axis-preserving isomorphism for phi. Restricting this displayed family
at a parameter x gives precisely t_x^*L divided by L with the two constant factors
that normalize its value at the identity, as the node's proof explains. No choice of
a basis of e_A^*L is used.

11. Pullback dual homomorphisms: `DualHomomorphisms` quantifies over every B of the
same kind, every representing dual E and universal Q with axes, and every a:A to B
preserving the GIVEN group laws. It supplies aDual:E to D, proves IsHom for it, and
characterizes it uniquely among all maps by Dualizes. That predicate compares
literally (a x identity_E)^*Q and (identity_A x b)^*P on A x E. The last conjunct
requires the displayed normalized isomorphism to pull back to the normalized
isomorphism after every locally Noetherian base change.

12. Base change, including geometric fibres: `UniversalBaseChange` quantifies over
all locally Noetherian T over the base. Pointed.baseChange and baseChangeProductMap
are actual sheaf pullbacks with their projections. The resulting A_T,D_T retain the
abelian geometry; the actual pullback of P represents the same all-scheme functor.
`IsBaseChangedAxes` fixes its two axis maps to the pullbacks of the original maps
through the fixed tensor/unit compositors, rather than allowing unrelated
trivializations. CanonicalAxisEquivalent in the identities, difference and dual-map
clauses asserts the base-change equality of each actual isomorphism. The literal
formula for N_L and the product maps pull back term by term. Uniqueness of their
classifying maps identifies the base-changed homomorphisms. Algebraically closed
field test schemes are among these T. Keeping the ambient algebraic-space category
over S and using the represented T is the equivalent slice presentation of spaces
over T, avoiding an extra small-site universe assumption.

13. Identity and composition: `ComparisonCoherence` says there exists a normalized
DualComparison with every other representing datum and that this WHOLE structure
is subsingleton. It retains both the space isomorphism and universal-line map, its
base equality, zero equality and both restricted-map equalities. Thus identity and
composites, formed with the existing pullback compositors, agree as the same
normalized comparison. UniversalBaseChange repeats that full comparison property
for the actual pulled-back data. This is uniqueness of actual comparisons, not an
unconstrained existence of an isomorphism or a chosen map.

### Why the normalization predicate is equivalent

AxisEquivalent quantifies over all pairs of compatible axis trivializations rather
than choosing tensor-evaluation normalizations inside the statement. This includes
the canonical normalization and determines its unique isomorphism. Conversely, for
these proper smooth geometrically connected factors, every unit on either axis and
on the product comes from the base, universally. Two compatible pairs of
trivializations differ by the SAME base unit (their intersection fixes that unit).
Scaling a canonical isomorphism by that unit gives the unique isomorphism for the
new pair. This is exactly the universal H0/axis-unit argument already in proof step 3
of the item. Consequently this predicate neither drops the canonical axis requirement
nor adds a new geometric hypothesis. CanonicalAxisEquivalent additionally compares
the ACTUAL pullback of the normalized isomorphism with the pulled-back axes, so it
does not hide the asserted base-change compatibility.

### Dependency declarations and imports

Original statement dependencies: Mathlib.AlgebraicGeometry.Scheme, Scheme and
Scheme.Hom; Mathlib.AlgebraicGeometry.Noetherian, IsLocallyNoetherian;
Sheaf.AlgebraicGeometry.AlgebraicSpace, AlgebraicSpace, EtaleSite, Modules and
IsLineModule; WeilConjectures.AlgebraicGeometry.Modules.Invertible,
Scheme.Modules.IsInvertible (through the restriction/line equivalence and algebraic
equivalence predicate).

Reused additional interfaces, read in their source files:

- Sheaf.AlgebraicGeometry.RegularGroupSpace: CommutativeSpaceGroup, its identity,
  groupSpaceBase, groupSpaceProjection, groupSchemeMap.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties: MapIsLocally,
  MapIsLocallyOfFinitePresentation, MapIsProper and its three component predicates.
- Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite: schemeSpace, enlargedFibreProduct;
  the existing fibreProduct_isAlgebraicSpace proves its algebraic-space property.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel: SmallModules,
  smallStructureSheaf, smallStructureRings, smallModuleRestriction,
  smallModuleEquivalence; the inverse extends small-model modules to the full site.
- Sheaf.AlgebraicGeometry.SpaceDerivedTensorPullback: smallModuleTensorPullback,
  its ordinary inverse-image part only, not the derived functor.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations: moduleTensorPullback;
  Sheaf.AlgebraicGeometry.SpaceFlatDirectImageBaseChange: moduleTensorComposition;
  Sheaf.AlgebraicGeometry.RigidifiedLines: rigidifiedUnitIso, the fixed local-tensor
  unit comparison. Our compositor/unit transport is conjugation by the existing
  equivalence, with no new arbitrary isomorphism.
- Sheaf.AlgebraicGeometry.SpaceAffineSectionsCompositors: smallModuleUnitIso,
  the fixed identity restriction of the structure module.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction: schemeRestriction, the
  restriction to ordinary modules on the underlying scheme of an etale chart.
- Sheaf.AlgebraicGeometry.LineAlgebraicEquivalence:
  Scheme.Modules.AreAlgebraicallyEquivalent and its LineAlgebraicEquivalenceStep.
- WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs: IsAbelianVariety.
- WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal and InternalHom:
  SheafOfModules.monoidalCategory and SheafOfModules.homObj. No tensor operation
  or internal Hom is invented or selected by a nonunique existence statement.

Plain proof imports: Mathlib.AlgebraicGeometry.Morphisms.Smooth (the smooth-flat and
local-finite-presentation instances); WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic
(IsAbelianVariety.geometricallyIntegral and irreducibleSpace);
WeilConjectures.AlgebraicGeometry.AbelianVariety.Projective
(exists_isClosedImmersion_projectiveSpace and exists_isAmple); and the newly landed
Sheaf.AlgebraicGeometry.AbelianVariety.PolarizationCalculus
(IsAbelianVariety.exists_dual_polarization_calculus). Their signatures/docstrings were
read. The field theorem remains only a proof ingredient. The other five proof-only
nodes in the existing proof_deps had no Lean records when inspected; their textual
proof roles remain intact in the main docstring, with no invented unused interface.

### Edge cases checked

The empty base is allowed: all geometric-fibre conditions are vacuous there and the
module/unit comparisons retain their actual empty-site interpretation. No nonempty
base, positive dimension or characteristic hypothesis is added. A dimension-zero
abelian fibre and the trivial group are included. Nilpotent bases and nonreduced,
non-Noetherian scheme parameters are included in Represents and RigidAutomorphisms.
Disconnected locally Noetherian bases are allowed. All tests use the fixed scheme
universe, so no smaller test universe makes a condition vacuous. Scheme models of
geometric fibres are required by actual cartesian squares, and FibrewiseTrivial tests
EVERY such model rather than a noncanonical selection. RigidAutomorphisms explicitly
also tests lines outside Picard zero. The identity-line term in N_L is retained on
nontrivial bases. Both identity and arbitrary locally Noetherian base changes are
included, without flatness assumptions on the base-change map.

### Searches

All service searches used the prescribed msearch.py NO wrapper and were logged in
searches.jsonl. LeanFinder query "Dual abelian algebraic space represents rigidified
algebraically trivial line modules and Poincare biextension" returned eight hits:
CommRing.Pic.functor, mk_dual, mk and inv_eq_dual, AffineSpace functor/point formulas,
and FGModuleCat.rightRigidCategory. None states relative duality. Loogle "Poincare"
returned zero. Mathlib grep AbelianSpace|Poincare|biextension in AlgebraicGeometry
returned zero.

LeanSearch "Normalized Poincare biextension on a relative abelian algebraic space
with axis preserving identities" returned eight unrelated normalization/coherence
hits. LeanFinder "Relative abelian algebraic space with normalized Poincare universal
module identity axis rigidifications and line module algebraic equivalence" returned
eight AffineSpace formulas. Loogle "Poincare", "Picard" returned zero. Mathlib grep
AbelianFamily|Poincare|DualAbelian in AlgebraicGeometry returned zero. These exact
queries, returned declaration names and dates are recorded in the new node.

Project rg searched lean/WeilConjectures and lean/Sheaf. The upstream Poincare hits
are cohomological duality, not dual abelian spaces. The node-id grep in
lean/WeilConjectures returned no match. The project now has the field-only
AbelianDualPoincareDatum and its polarization theorem, which were read and reused as
proof inputs. Its base is Spec k and its objects are schemes, so it supplies no
relative algebraic-space predicate. DAG grep for relative/Poincare also returned
generic ringed-site Picard/cup/pairing nodes: these concern H1 and units/torsors,
not representing relative dual spaces or normalized universal modules. Their records
were checked. blueprint_refs.py search 'relative abelian' returned zero; the earlier
'abelian space' search returned zero and 'Poincare' returned 46 cohomological or
unrelated matches. Existing component definitions were reused as listed above.

## New nodes

`def-sfb-abelian-space-poincare-data` introduces only the absent relative pointed
geometry, geometric-fibre predicate, universal-family/axis predicates and exact
comparison formulas needed to read this item. It uses the recorded small ringed-model
and module operations, existing line predicate and algebraic equivalence relation,
and existing natural commutative group structures. It does not assert existence of
a dual. Its source is Milne I Sections 8--9 with the relative use in Deligne 4.1.
The new node explicitly includes the elementary terminal-base fact needed for product
maps, and baseMap_eq has a complete elementary Yoneda proof docstring. Every other
helper has actual data or is an unfolding predicate. The three search kinds above
found no existing relative definition. In particular the field-only normalized datum
and generic ringed-site Picard comparison are not duplicates of this notion. No
original dependency record needed replacement.

## Second reading by NO

The dispatcher expressly prohibits other agents. This is an additional reading by
the same worker, not a claim of independent review; the maintainer's independent
review is still required. I reopened the node, both modules and the additional
interface records and checked the numbered correspondence above against the actual
binders and definitions.

I checked especially: the fibre predicate uses a cartesian scheme model over every
algebraically closed field; all group operations refer to the supplied laws;
FibrewiseTrivial uses AreAlgebraicallyEquivalent after actual scheme restriction;
Represents quantifies over all T, whereas only the asserted base-change clause has
IsLocallyNoetherian T; RigidAutomorphisms has no algebraic-triviality guard; and
Axes compares at the intersection using canonical unit/composition maps.

During that reading I separated bare classifying uniqueness from its base-change
property: ClassifiesDifference and Dualizes now use AxisEquivalent alone, while
DifferenceHomomorphisms and DualHomomorphisms assert CanonicalAxisEquivalent for the
unique selected map separately. Thus uniqueness is not silently restricted to maps
whose comparisons already satisfy the base-change conclusion. I also checked the
literal four factors of difference (including e-star L), both triple-product
projection indices, and the directions A to B / E to D of the dual map. For the new
node, I verified its statement names every component declaration and its stmt_deps
are exactly its bracket citations; it contains no relative existence assertion.
The terminality helper is explicitly part of that definition node and has only a
sorry proof. The only elaboration repair was making the represented identity chart
reducible and rewriting Yoneda's map of identity explicitly; it changes no geometry.

Both modules compiled separately against the live published build using scompile.py,
including the private overlay for the imported sibling. The final run reported
14.0 seconds for the definition library module and 6.0 seconds for the theorem library
module, with no errors or warnings printed. No lake/global build was run. Delivery
preflight and per-file compilation are performed again by the required wrapper.

The first dry run requested the schema-required empty import_flags field on the new
definition node; it was added following the existing definition-node format.
