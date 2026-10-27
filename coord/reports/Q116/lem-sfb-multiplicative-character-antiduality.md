## Worker report

Item: `lem-sfb-multiplicative-character-antiduality`, Q116, stage 2, 2026-10-24 UTC.

The delivery states `AlgebraicGeometry.MultiplicativeType.multiplicative_character_antiduality`
in `Sheaf.AlgebraicGeometry.MultiplicativeCharacterAntiduality`. Its only proof is `sorry`.
The companion definition module `Sheaf.AlgebraicGeometry.MultiplicativeCharacterData`
has actual definitions and no postponed proofs or choices. The item gains only its `lean`
record and one statement dependency, `def-sfb-multiplicative-character-data`.
Its mathematical statement, proof plan, and original dependencies are preserved.

Source read: Milne, Algebraic Groups, printed pp.230--234 (PDF pp.242--246),
pp.239--241 (PDF pp.251--253). In particular Section 12(a) defines characters
and their addition, Theorem 12.9 gives the split antiequivalence and exactness,
and the text before Theorem 12.23 constructs the inverse from semilinear invariants.
The finite-Galois version of the construction is the node's finite-stage form of
that same invariant algebra. Corollary 12.25 supplies the split scalar-extension argument.

Hypotheses and clauses, in the order of the node:

1. A field and fixed separable closure are `(k ks : Type u) [Field k] [Field ks]`
   `[Algebra k ks] [IsSepClosure k ks]`. The latter is the actual Mathlib notion
   reexported by the recorded separable-closure dependency.
2. Affine group schemes of finite type are `FiniteTypeGroups k`, the full subcategory
   of `Grp (Over (Spec (.of k)))` satisfying `IsAffine G.X.left`,
   `LocallyOfFiniteType G.X.hom`, `QuasiCompact G.X.hom`, and
   the recorded `IsMultiplicativeType G`. No commutativity, reducedness,
   connectedness, smoothness, or characteristic restriction is added.
   Group homomorphisms are all morphisms in this full category.
3. The geometric closed embedding into a finite product of G_m is exactly the
   existing `IsMultiplicativeType`, whose definition uses `AlgebraicClosure k`,
   `splitTorus`, and `IsClosedSubgroupScheme`. Rank zero is included.
4. The group algebra, its indexed basis and all three Hopf operations are the
   existing `diagonalizableGroup`, implemented through `AddMonoidAlgebra` and
   Mathlib's `hopfSpec`. This is reused, not reconstructed in the delivery.
5. The first conjunct explicitly gives for every G an intermediate field L inside ks,
   `FiniteDimensional k L`, `Algebra.IsSeparable k L`, a finitely generated
   `M : AddCommGrpCat`, and a group-scheme isomorphism `G_L ≅ diagonalizableGroup L M`.
6. `E : (FiniteTypeGroups k)ᵒᵖ ≌ CharacterModules k ks` is the contravariant equivalence.
   The target is the full category of `Action AddCommGrpCat (ks ≃ₐ[k] ks)` with
   `AddGroup.FG M.V` and open stabilizers of every element. Thus torsion is allowed,
   and continuity is precisely continuity for a discrete underlying abelian group.
   `krullTopology` is the Mathlib topology whose identity neighborhoods are generated
   by fixing finite intermediate fields. In a separable closure these fields are separable.
7. `e G` identifies the underlying abelian group of E(G) bijectively with the actual
   `GeometricCharacters ks G.obj`. These are group-scheme morphisms
   `G_ks ⟶ (G_m)_ks`, not homomorphisms on rational points. The target is the
   pulled-back recorded G_m, canonically G_m over ks with Laurent Hopf law.
   The first displayed equality for `e` states that x+y is pointwise multiplication
   of the two underlying character morphisms. Bijectivity and this equality also
   identify zero and negatives, so no separate or arbitrary abelian group structure
   on the character set is assumed.
8. The next conjunct is `IsConjugate σ (e G m) (e G (ρ σ m))`.
   `IsConjugate` uses the unique semilinear scheme maps determined by BOTH projections
   of the scalar-extension pullbacks. The equality is `a ≫ χ = ψ ≫ b`, which on the
   Laurent coordinate says that the coefficient of ψ is σ applied to that of χ.
   It is exactly conjugation, including the direction of σ. This universal condition
   is not vacuous: the maps exist uniquely by the pullback universal property, since
   σ fixes k. It supplies no arbitrary map or extra hypothesis on G.
9. For `f : G ⟶ H`, the following conjunct identifies E(f.op) with
   `(baseChange (K := ks)).map f.hom ≫ e H m`. This is pullback of characters,
   with the required identity/composition laws already supplied by the functor E.
10. The closed-immersion clause is
    `IsClosedImmersion f.hom.hom.hom.left ↔ Function.Surjective (E.functor.map f.op)...`.
    Its source and target are exactly X*(H) and X*(G), in the correct reversed order.
11. Every continuous finitely generated M explicitly has a
    `L : FiniteGaloisIntermediateField k ks` and a finite-stage action ρ whose composite
    with `AlgEquiv.restrictNormalHom L.toIntermediateField` is the original action.
    This is an existence conclusion, not an assumed splitting field.
12. For EVERY finite Galois intermediate field and EVERY factoring action ρ, the
    inverse-model conjunct gives `d : InvariantHopfModel M.obj.V ρ`.
    The invariant algebra is the actual `invariantGroupAlgebra M.obj.V ρ`:
    the intersection of the equalizers of
    `semilinearGroupAlgebra M ρ σ` and the identity, where the former is precisely
    the coefficient map σ followed by the label map ρ(σ).
    Its value on a*e_m is σ(a)*e_(ρ(σ)m).
13. The field `d.hopf` is a Hopf structure on that specified subalgebra, not on an
    unspecified chosen ring. `d.split` is a group isomorphism over L to D_L(M),
    and `d.split_projection` says its inverse followed by the scalar projection
    is `Spec.map` of the invariant-algebra inclusion. Thus the pulled-back Hopf
    operations are exactly the standard ones on L[M]. Faithful scalar extension
    determines the descended operations. No data definition contains `sorry`.
14. `i` identifies E's inverse on M with the spectrum of that actual invariant algebra
    with `d.hopf`. `s` is its splitting over ks, with its scalar projection explicitly
    normalized by the coefficient inclusion L[M] → ks[M]. The final equation in this
    conjunct says the character corresponding to m through E's counit, transported
    by i and s, has Laurent coordinate `AddMonoidAlgebra.single m 1`.
    This fixes the indexed character identification, rather than merely asserting
    that two unspecified group schemes happen to be isomorphic.
15. The natural identifications in the node are E's unit and counit, with `e` identifying
    its functor with the actual character functor and the preceding indexed equation
    identifying its inverse with the specified D(M). Independence of L and of its
    character identification is expressed by the universal quantifier over all factoring
    finite Galois fields and the same fixed inverse E: transport through E gives an
    isomorphism between any two models, preserving every m. Full faithfulness makes
    it unique and makes the three-choice coherence automatic.
16. Arbitrary scalar extension quantifies over fields `K Ks`, their algebra structures,
    `[IsSepClosure K Ks]`, and compatible towers k→K→Ks and k→ks→Ks.
    There is no finite, algebraic, separable, or purely inseparable condition on K/k.
    `ext G` is an equivalence between X*(G) and actual characters of `(G_K)_Ks`.
    Its target is the twice pulled-back original G_m, again canonically G_m over Ks.
17. `IsCharacterExtension (e G m) (ext G m)` fixes this equivalence to the canonical
    extension map: the comparison maps to G_ks and (G_m)_ks preserve the projections
    to the original schemes and lie above the specified embedding ks→Ks.
    Existence and uniqueness of those maps follow from the compatible towers and the
    pullback universal property; no independent comparison maps are assumed.
18. The next two clauses give preservation of character addition and naturality for
    EVERY group homomorphism f, using the two actual base-change functors on f.
19. For every τ in Gal(Ks/K) and σ in Gal(ks/k) agreeing on ks, the last scalar clause
    gives `IsConjugate τ (ext G m) (ext G (ρ σ m))`.
    The displayed compatibility `τ (algebraMap ks Ks a) = algebraMap ks Ks (σ a)`
    is the defining equation for the restriction Γ_K → Γ_k. Since ks/k is normal
    separable and algebraic, every τ has exactly one such σ. This expresses the
    restricted action without choosing an arbitrary homomorphism of Galois groups.
20. The final conjunct supplies a split group isomorphism `(D_k(M))_K ≅ D_K(M)`
    for every abelian M. Its inverse followed by the scalar projection is explicitly
    `Spec.map` of the coefficient map `k[M] → K[M]`.
    This is the canonical isomorphism with basis formula λ⊗e_m ↦ λe_m.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, `algebraMap`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`, `Grp`, and group-object morphisms.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `IsSubgroupScheme`, `IsClosedSubgroupScheme` and its recorded group-scheme interpretation.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`: `multiplicative`, `multiplicativeGroup`,
  with the affine spectrum and Laurent Hopf law stated by its dependency node.
- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`: `AlgebraicClosure`;
  `IsAlgClosure` / `IsAlgClosed` were read in `IsAlgClosed.Basic`.
- `WeilConjectures.Mathlib.FieldTheory.IsSepClosed`:
  `IsSepClosure.exists_intermediateField_mem` and its public `IsSepClosure` interface.
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`:
  `baseChange`, `splitTorus`, `IsMultiplicativeType` (through the new definition node).
- `Sheaf.AlgebraicGeometry.DiagonalizableGroup`:
  `diagonalizableGroup` (through the new definition node), with its coordinate definition
  and the recorded contravariant `diagonalizableGroupMap` read in that file.

The new definition node also uses Mathlib's `Action`, `ObjectProperty.FullSubcategory`,
`krullTopology`, `AddGroup.FG`, `AddMonoidAlgebra.mapAlgHom`,
`AddMonoidAlgebra.mapDomainAlgHom`, `AlgHom.equalizer`, the subalgebra lattice,
`hopfSpec` and `Scheme.ΓSpecIso`. Its `InvariantHopfModel` is a data structure
specifying the descent property, not an existence theorem or a chosen descent object.

Available proof dependencies are imported privately: `FiniteGaloisIntermediateField.adjoin`
from `Galois.GaloisClosure`, the group-like-basis result from `Bialgebra.MonoidAlgebra`,
and group-like Hopf operations from `HopfAlgebra.GroupLike`. The affine Hopf dictionary,
affine spectra and closed immersions are already publicly reachable through statement
imports. The proof nodes `lem-sfb-split-torus-subgroups-diagonalizable`,
`lem-sfb-geometrically-diagonal-coalgebra-separable-basis`, and
`lem-sfb-galois-hopf-algebra-descent` have no recorded declarations in the read clone;
there are no corresponding importable modules to add. They remain proof dependencies,
and their exact uses appear in the seven-step theorem docstring.

Edge cases checked against the statement and the source:

- The trivial group and M=0 are included; `splitTorus k 0` is the trivial group.
- Finite torsion M, in particular Z/p in characteristic p (giving non-smooth μ_p),
  are allowed. There is no smoothness, reducedness or torsion-free hypothesis.
- Finite separable splitting may be the trivial field extension; finite Galois L=k
  with the trivial action is included in the universal inverse-model clause.
- Infinite Galois groups and infinite finitely generated abelian groups are included;
  continuity is open stabilizers, not finiteness of M or of the absolute Galois group.
- Identity extensions K=k, purely inseparable extensions and transcendental extensions
  all fit the scalar-extension block. Closures and their embeddings are arbitrary
  subject only to the stated compatibility. No isomorphism of Galois groups is assumed.
- All groups, fields and index types use an explicit ambient universe u, as the recorded
  scheme/base-change interface does. No finite-cardinality bound or equality of distinct
  site object/morphism universes is imposed; there are no auto-bound variables.
- The split extension clause includes arbitrary abelian M, as the indexed group-algebra
  scalar-extension formula requires no finite generation.
- `IsConjugate` and `IsCharacterExtension` quantify over uniquely determined pullback
  maps; their projection conditions have actual canonical solutions. They do not assert
  a property of arbitrary unconstrained maps or rely on an impossible premise.

Searches for an existing statement or missing notion:

- msearch LeanFinder: "Character antiequivalence for affine group schemes of multiplicative
  type over a field with Galois action and scalar extension". Eight unrelated Galois-group,
  analytic representation/character hits; no group-scheme antiequivalence.
- msearch Loogle: "Grp, AddCommGrpCat, HopfAlgebra, IsSepClosure". Zero hits; service reported
  the short identifier `Grp` unknown. Local source inspection resolved the actual namespaces.
- msearch LeanSearch: "group scheme characters Galois action multiplicative type equivalence".
  Eight hits involving `MulChar`, ordinary additive characters and `IsGaloisGroup`; none match.
- msearch grep: "characterFunctor|IsMultiplicativeType|diagonalizableGroup|characterAntiequiv".
  Zero Mathlib hits. `rg` in `lean/WeilConjectures` found no such specialization; in
  `lean/Sheaf` it found the existing D(M) and multiplicative-type definitions and consumers,
  which are reused. Searching the item id in `lean/WeilConjectures` found no declaration.
- New-interface msearch LeanSearch: "category of finitely generated discrete abelian Galois
  modules and group scheme characters with semilinear invariant group algebra".
  Eight generic FDRep/FGModuleCat/finite Galois-category hits, no specialized interface.
- New-interface msearch LeanFinder: "Category of finitely generated discrete abelian Galois
  modules character group schemes semilinear invariant group algebra".
  Eight generic Galois/Tannaka/FDRep hits. Existing `finGaloisGroupFunctor` supplies finite
  Galois data, not the character category or the canonical coordinate conditions.
- msearch grep and local `rg` over Mathlib, WeilConjectures and Sheaf:
  "CharacterModules|GeometricCharacters|invariantGroupAlgebra|semilinearGroupAlgebra".
  No hits before this delivery. The new node stores the search outputs verbatim.
- `tools/blueprint_refs.py search 'character antiduality'`: zero blueprint matches;
  DAG text/name searches found no node defining the combined character/descent interface.
  DAG searches did find `def-sfb-diagonalizable-group` and
  `def-sfb-tori-multiplicative-type`; these supply the existing constructions used here.
- `tools/blueprint_refs.py ancestor` reported `blueprint.from.node = None`, matching the
  item's current supporting-node ancestry. The new node retains that ancestor and prepends
  this item to `blueprint.from.via`.

No statement dispute, correction, or unusable dependency record was found.

Validation: both files were compiled separately in dependency order through the prescribed
`scompile.py`, in module mode with explicit public statement imports. The final source
checks have no errors or warnings; sorry warnings are disabled by the project as documented
in brief-stage2. Every delivered line is at most 100 characters. Dry-run and delivery
results are recorded by the delivery wrapper.

## New nodes

`def-sfb-multiplicative-character-data` defines the specialized character interface absent
from the source: the full categories of affine finite-type multiplicative-type groups
and discrete finitely generated Galois modules; actual geometric character hom-sets;
projection descriptions of conjugation and character extension; the explicit semilinear
group-algebra maps and invariant subalgebra; its specified Hopf-model data; and the Laurent
coordinate of a character. The source is Milne Sections 12(a)--(b) and 12(g), pp.230--233,
239--240. Every construction is actual data: full subcategories, pullback projections,
composites of recorded algebra maps, equalizers and spectra. There is no existence choice
and no postponed theorem in this module. The node cites the existing D(M), scalar extension,
multiplicative-type, group-scheme, finite-type, G_m, field and spectrum nodes. Search outputs
are in its `mathlib_searches`; the generic Mathlib action/category/algebra pieces exist,
but their specialized character/descent interface did not. The theorem explicitly asserts
existence of the required Hopf model and fixes its operations by the standard scalar splitting.

## Second reading by Q116

I reread the finished node, its new definition node and both source files in a separate
pass. This is a second pass by the assigned worker; no additional agent was started.
The maintainer's independent review remains the independent reading of this delivery.

The source category has exactly affine finite-type groups of multiplicative type, and the
target uses all finitely generated abelian groups with open stabilizers, including torsion.
The character equivalence is bound to actual group-scheme maps, with addition, Galois
conjugation and natural pullback all specified. Its inverse is tied to the actual invariant
subalgebra and to each basis label via the counit. The universal quantification over
factoring L gives independence of L. The scalar-extension maps are characterized by both
pullback projections and the Galois compatibility uses restriction on coefficients.

This pass found two clauses worth making explicit: existence of a finite Galois field
through which each module action factors, and the coordinate normalization of split scalar
extension. Both were added to the final theorem before its final successful compile.
The inverse model's projection equality was checked to specify the Hopf law rather than
only an arbitrary group isomorphism. The character-label equation transports the counit's
inverse in the correct direction. The conjugation equation has σ, not σ inverse, on the
coordinate coefficients. No mathematical statement correction was required.
