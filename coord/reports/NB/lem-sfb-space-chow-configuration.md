## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceChowConfiguration` states
`AlgebraicGeometry.AlgebraicSpace.exists_space_chow_configuration`, with its proof
postponed by `sorry`. The only auxiliary definitions are `chowConfigurationBase`,
`chowAbsolute`, and `chowAbsoluteMap`: they explicitly use Spec of ULift Z, its
terminal structure map, and the given scheme morphism, respectively. Their data
contain no `sorry`, choice of an arbitrary object, or extra mathematical hypothesis.

Source read: `literature/stacks-project/spaces-cohomology.tex`, Tag 089J,
`lemma-weak-chow`, from the affine atlas through the construction of Xprime and
its glued map, and the coordinate-completeness paragraph in the proof of the claim.
The node covers that construction, not the properness claim or induction. Its
natural-language statement and proof are preserved verbatim. The theorem docstring
reproduces the eleven proof steps, including the zero-ideal overlap argument.

The statement is expressed by existentially supplying the representing schemes
and their universal properties, rather than choosing unspecified data in a definition.
In particular these witnesses cannot be unrelated schemes satisfying only the
conclusions. The F universal property fixes the sheaf fibre product with all its
projections. The Fan limit fixes the product over B, the map a is fixed by its
coordinates, and Z is literally `a.left.image`, with its canonical factor and inclusion.

Hypothesis correspondence:

| Node hypothesis or convention | Lean rendering |
| --- | --- |
| Work over Spec Z | `chowConfigurationBase = Spec (.of (ULift ℤ))`; `chowAbsolute` uses `specULiftZIsTerminal.from`. |
| Schemes and spaces in the fixed universe bound | Explicit `universe u`, `Scheme.{u}`, `CommRingCat.{u}`, `AlgebraicSpace chowConfigurationBase`, and test fields `Type u`. There is no independent smaller test universe. |
| Sheaf fibre products and atlas topology | The existing presheaves of algebraic spaces, `IsPullback`, `Point`, `pointImage`, and its existing `pointTopologicalSpace` are used. |
| Separated, quasi-compact, quasi-separated, local finite type/presentation, finite type/presentation, proper conventions | The already-landed `MapIsSeparated`, `MapIsFiniteType`, and `IsRepresentableWith` definitions are used. `MapIsFiniteType` is exactly existing quasi-compactness and chartwise `LocallyOfFiniteType`; properness of the scheme projections is Mathlib `IsProper`. No extra finite-presentation or properness assumption on X is imposed; the paragraph defining these terms supplies conventions. |
| B = Spec A for any commutative ring | `A : CommRingCat.{u}` and `Spec A`. |
| X -> B separated of finite type | `s`, `hs : MapIsSeparated s`, `hft : MapIsFiniteType s`. |
| Affine W of finite type over B | `W : Over (Spec A)`, `hWa : IsAffine W.left`, `hWft : LocallyOfFiniteType W.hom ∧ QuasiCompact W.hom`. |
| Representable surjective etale f: W -> X over B | `f`, `hf : IsEtale f.hom.hom`, `hfs : IsSurjective f.hom.hom`, and the structure-map equality `hfsB`. `IsEtale` includes representability. |
| Positive integer geometric fibre bound d | `d : ℕ`, `hd : 1 ≤ d`; `hbound` asserts finiteness and `Nat.card ≤ d` for the lift set above every algebraically closed field-valued x. Finiteness is explicit, so the zero convention of `Nat.card` for infinite types cannot lose the bound. |
| The exact degree-d locus U is open | `U : OpenSubspace X`; `hU` identifies its sections on every geometric point with the locus where that lift set has cardinality d. |
| W_U -> U finite etale of degree d | `hUfinite` applies the existing `IsRepresentableWith` to the actual presheaf pullback projection and tests `IsFinite p.left ∧ Etale p.left`. Together with `hU`, its geometric fibres all have d points. For a finite etale algebra, its finite locally free rank at a geometric point is the number of points in that geometric fibre, so this is precisely rank d, not a condition only on K-rational lifts over nonclosed fields. |
| Chosen W -> Y -> projective m-space over B, m >= 0 | `Y : Over (Spec A)`, `j : W ⟶ Y`, `hj`, `m : ℕ`, `eY`, `heY`, `heYB`. Homogeneous coordinates are `ULift (Fin (m + 1))`; no dimension or nonemptiness assumption is added. |

Conclusion correspondence, in order:

| Node construction or assertion | Lean rendering |
| --- | --- |
| F = the d-fold sheaf fibre product | Existential `F`, projections `π`, and map `q`; `∀ i, yoneda.map ... ≫ f = q` together with the universal `∃! l` for every scheme T, common image x, and compatible tuple a. Because d >= 1, these are the ordinary d-fold fibre product over X; using Over B for F and its projections retains the induced B-structure. |
| F is affine | `IsAffine F.left`. |
| V is the complement of all pairwise equality diagonals | `V : F.left.Opens` with its set equal to the complement of the union of the ranges of `equalizer.ι (π i).left (π k).left` for `i ≠ k`. The equalizer represents equality of the two coordinates, including residue-field information. |
| V is quasi-compact open and closed in F | Openness is part of `V : F.left.Opens`; closedness is `IsClosed (V : Set F.left)`; quasi-compactness is `CompactSpace V.toScheme`. |
| Product Y^d_B and the specified V -> product | `T : Over (Spec A)`, projections `ρ`, `Nonempty (IsLimit (Fan.mk T ρ))`, and the coordinate equations for `a : Over.mk (V.ι ≫ F.hom) ⟶ T`. These fix a uniquely by the product universal property. |
| Z is the scheme-theoretic image, with projections g_i | Literal `a.left.image`, `a.left.imageι`, `a.left.toImage`; each g_i is `a.left.imageι ≫ (ρ i).left`. No substitute closed subscheme is quantified. |
| V -> Z is quasi-compact open and both kinds of dense | `IsOpenImmersion a.left.toImage`, `QuasiCompact ...`, `IsSchemeTheoreticallyDominant ...`, `DenseRange ...`. |
| Each g_i is proper | `∀ i, IsProper (a.left.imageι ≫ (ρ i).left)`. |
| Z has a closed immersion into finite projective space over B | Existential `N : ℕ`, `eZ`, `IsClosedImmersion eZ`, and its B-structure-map equality. |
| H is the union of the inverse images g_i^-1(W) | `H : a.left.image.Opens` and the exact set equality with the union of preimages of `Set.range j.left`. |
| H is quasi-compact and separated | `CompactSpace H.toScheme ∧ H.toScheme.IsSeparated`. |
| H has a quasi-compact immersion into finite projective space over B | Existential `N`, `eH`, `IsImmersion eH`, `QuasiCompact eH`, and the B-structure equality. |
| The local f g_i maps agree on overlaps and glue to p | Each local chart is the actual scheme pullback `pullback g_i j.left`, with maps `k i` to H satisfying `k i ≫ H.ι = pullback.fst ...`. Its composite with `p` equals `pullback.snd ...` followed by f. These equations assert that p restricts to every prescribed map; on each overlap the two restrictions therefore agree. The charts cover H by its exact union formula. |
| p is over B, separated, and finite type | The displayed equality for `p.hom.hom ≫ s.hom.hom`, and `MapIsSeparated p ∧ MapIsFiniteType p`. |
| V is contained in H, and dense there in both senses | `r ≫ H.ι = a.left.toImage`, `IsOpenImmersion r`, `QuasiCompact r`, `IsSchemeTheoreticallyDominant r`, and `DenseRange r`. Thus r is the actual factor of V -> Z through H. |
| V -> H -> X factors through U and surjects onto U | `vU`, its equation with `U.val.ι`, and `pointImage vU = Set.univ` in the point set of `U.val.toFunctor`. This is surjectivity on the prescribed point classes, not sectionwise surjectivity over arbitrary schemes. |
| Every K-valued v splits the fibre into the d coordinate copies of Spec K | The final clause takes K, v, any L, and any `b : K →+* L`. Taking L = K and b = identity gives the K assertion. P and w represent the actual fibre, by the asserted `IsPullback`. The morphisms `c i` are over Spec L and their composites with w are the corresponding coordinates of v after `Spec.map (CommRingCat.ofHom b)`. `Nonempty (IsColimit (Cofan.mk P c))` says these specified maps exhibit P as the coproduct of d copies of Spec L in schemes over L. |
| The very identification remains true after every field extension | The same final clause quantifies over every L and b, with coordinate labels fixed by the formula using `π i`. The canonical comparison with the pullback of the K coproduct preserves each labelled injection by these equations and hence is uniquely fixed by the coproduct universal property. No arbitrary unlabelled isomorphism replaces it. |

Dependency declarations used, with source modules read:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Spec`, `Spec.map` (def-pc-scheme and def-weil-affine-spectrum).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsRepresentableWith`, `IsEtale`, `IsSurjective` (def-trf-algebraic-space).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`: `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, `etale_fibreProduct_isScheme` (lem-trf-space-fibre-products-etale-covers).
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `PointRepresentative.map`, `pointImage`, `pointTopologicalSpace`, using the existing `Point` from AlgebraicSpacePointClasses (def-a1-space-point-topology).
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`; `Mathlib.AlgebraicGeometry.Morphisms.Immersion`: `IsImmersion` (def-weil-closed-immersion).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`; `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact` (def-weil-finite-type-morphism).
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation` (def-sbc-locally-finite-presentation, retained in the imported conventions).
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `.Separated`, `.UniversallyClosed`: `IsProper`, `IsSeparated`, `UniversallyClosed` (def-weil-proper-morphism).
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`: `ProjectiveSpace`, `ProjectiveSpace.over` (def-nagata-projective-space-base-change), using m+1 homogeneous coordinates.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion` (def-weil-open-immersion).
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale` (def-weil-etale-morphism).
- `Mathlib.Algebra.Field.Defs`: `Field`, the Mathlib match of def-weil-field.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`: `Scheme.Hom.image`, `.imageι`, `.toImage` (def-nagata-scheme-theoretic-image).
- `Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant`: `IsSchemeTheoreticallyDominant` (def-nagata-scheme-theoretically-dense-open); for the quasi-compact open immersions used here, this is exactly injectivity of the structure sheaf map.
- def-weil-size-convention is the recorded metatheoretic convention, rendered by the explicit universes, with no fictitious declaration or import.

The only stmt_deps additions are three already-landed definition interfaces, without
new nodes: `def-sfb-space-morphism-properties` supplies MapIsSeparated/MapIsFiniteType
from AlgebraicSpaceMorphismProperties; `def-a1-space-open-subspace` supplies OpenSubspace
from AlgebraicSpaceOpenSubspace; and `def-trf-scheme-algebraic-space` is the existing:true
definition owner of schemeSpace in EnlargedEtaleRingedSite. This last module is imported
directly. The enlarged-etale-ringed-site theorem and SpaceCotangentRingMap are no longer
added/imported: the statement uses only the representable-sheaf embedding, whose actual
Yoneda data are retained by schemeSpace. This repairs H2 of return 6b5b587c46c4.
No dependency-node record is edited and no replacement definition is introduced.

Proof-only imports include the recorded modules for open-factor scheme tests,
representable-etale scheme tests, closed-immersion products, Segre products, and
etale-fibre discrete separable points, together with the Mathlib permanence modules
named by the proof's Mathlib leaves. The generic proof prerequisites with no Lean
record remain postponed proof inputs; the stage-2 theorem needs none as a hypothesis.

Edge cases checked before writing and on the completed signature:

- d = 1: the union of unequal-index equalizers is empty, V = F = W; the one-factor Fan is Y. The unique coordinate labels the one copy of the field.
- m = 0: `Fin (m+1)` has one homogeneous coordinate, hence this is projective zero-space, not the empty projective scheme.
- Empty U, and a nonsharp positive bound d: no assumption that U is nonempty is added. If every fibre has fewer than d points, V is empty; all its field-valued assertions have no input v and surjectivity onto empty U is valid.
- Empty schemes, including A the zero ring: no inhabitance or nontriviality assumption on A, W, X, Y, F, V, Z, or H was added. Products use d >= 1 and the canonical image of the empty map stays empty.
- Nonreduced A and nonreduced schemes: no reducedness is imposed, and the image is the actual kernel-ideal scheme-theoretic image; density uses the scheme predicate, not merely topological closure.
- Nonsplit fibres over K: the splitting assertion is conditional on a K-valued point v of the distinct configuration, not on an arbitrary point of X(K). Thus it does not claim arbitrary finite etale K-algebras split.
- Field extensions include identity and arbitrary extensions; no Algebra, finiteness, separability, or algebraic-closedness hypothesis is imposed on the final K or L. Ring homomorphisms between these fields are automatically injective.
- Equality diagonals use scheme equalizers. They do not identify different residue-field embeddings merely because their images have the same underlying point in W.

Searches for an existing statement (all run through msearch.py where applicable):

- leanfinder query `compactified configuration of distinct tuples of an affine etale atlas of a separated algebraic space Chow lemma`: eight hits concerning affine transition limits and affine/etale schemes; no configuration/closure/gluing statement.
- loogle query `AlgebraicGeometry.Scheme.Hom.image, AlgebraicGeometry.IsImmersion`: three hits, all the existing immersion-to-image interface; used it, but none asserts this node.
- grep query `distinctTuple|chow.*configuration|ChowConfiguration`, in Mathlib AlgebraicGeometry: zero hits.
- leansearch query `Chow lemma compactified distinct tuple configuration algebraic space affine etale atlas`: eight etale/affine-space/cover hits; no configuration statement.
- Direct rg in `lean/WeilConjectures` and `lean/Sheaf` for the node id and for `distinctTuple`, `ChowConfiguration`, and the new names: no existing matching statement or conflicting new name. Searches for morphism properties and scheme embeddings located the existing interfaces used above. The generic Chow lemmas found by the broader Chow search concern modifications of schemes and do not state this algebraic-space atlas configuration.

Validation: scompile.py compiled this module separately as both the sandbox module
and its actual library module. The initial draft had arrow-parenthesization errors,
a namespace collision with AlgebraicSpace.pullback, and an unqualified ofHom; these
were repaired by parenthesizing Hom-valued families, qualifying Limits.pullback, and
using CommRingCat.ofHom. No unbound implicit variables or diagnostic commands remain.
The final import-complete version is compiled again before the delivery dry run.

No statement dispute, source error, node correction, new node, or dependency-module
repair is needed. The declaration record contains the signature copied verbatim from
the theorem keyword through the result, excluding `:=`, and all four public names.

## Second reading by NB

Repair reading on 2026-10-24: I reopened the retained Lean module, the current main
node's complete statement, Tag 089J in spaces-cohomology.tex (lemma-weak-chow), and the
existing definition node def-trf-scheme-algebraic-space with its recorded declaration
in EnlargedEtaleRingedSite. This is a fresh clause-by-clause reading by this worker;
it does not assert that another agent performed the reading. I checked the following
against the actual binders and conjuncts, not only the earlier report.

1. The base is Spec of ULift Z, and every scheme and space has explicit universe u.
   A is CommRingCat, so the zero ring is allowed. The structure map s, its hs and hft
   binders, and hfsB render X/B separated finite type and the fact that f is over B.
   W is an Over B object, with its own IsAffine, local finite type and quasi-compact
   conditions. IsEtale and IsSurjective are the recorded representable scheme-test
   predicates. I found no missing base compatibility or extra reducedness condition.
2. hd is exactly 1 <= d. hbound quantifies over every algebraically closed field
   and every x, with both Finite and Nat.card <= d for the literal lift set. The
   Finite conjunct prevents the convention Nat.card of an infinite type = 0 from
   admitting an infinite fibre. U is the existing OpenSubspace, and hU is an iff
   with cardinality d, rather than mere containment in that locus. hUfinite tests
   the literal pullback projection for IsFinite and Etale; together these say finite
   etale rank d. There is no assumption that U is nonempty or d is the least bound.
3. Y, j and hj give the specified open immersion over B. eY and heY give the closed
   projective embedding; heYB checks it over B. The coordinate type is Fin (m+1),
   lifted into u, so m=0 means projective zero-space and is included.
4. The first existential F has d projections pi and q. The equations make each
   coordinate map to q, and the following forall T, x, a and exists-unique l is the
   universal property on every scheme test. Thus F represents the d-fold sheaf
   fibre product; it is not merely an affine scheme with some coordinate maps.
   IsAffine F.left is a conclusion. The Over B projections retain the B-structure.
5. V is an Opens of F, with exact carrier equal to the complement of the ranges
   of the coordinate equalizers for i != k. These are equality diagonals, not
   equality of underlying image points. IsClosed and CompactSpace then assert the
   remaining closed and quasi-compact clauses. For d=1 the unequal-index union
   is empty and this carrier equality gives V=F.
6. The next T and rho are in Over B; IsLimit (Fan.mk T rho) specifies Y^d_B.
   Each coordinate of a is V inclusion followed by pi and j, so the map a is fixed
   by the product property. All uses of Z are the literal a.left.image, with
   a.left.imageι and a.left.toImage. IsOpenImmersion, QuasiCompact,
   IsSchemeTheoreticallyDominant and DenseRange apply to this canonical factor.
   Thus neither a different closure nor merely a topologically dense image occurs.
7. Every g_i is the literal image inclusion followed by rho_i, with IsProper
   asserted for each. The existential eZ is a closed immersion into finite
   projective space and its displayed equation checks the B-structure. No fixed
   projective dimension or stronger embedding hypothesis is substituted.
8. H's carrier is exactly the union of the inverse images of Set.range j.left
   under those g_i. CompactSpace and H.toScheme.IsSeparated give both requested
   properties of H. eH is an IsImmersion and QuasiCompact into finite projective
   space, with the equation over B. Openness is carried by H : image.Opens.
9. The charts used for gluing are the actual Limits.pullback g_i j.left. The
   first equation for k_i pins it to the chart inclusion in Z; the second pins
   its composite with p to the map to W followed by f. The carrier union says
   these charts cover H. Consequently a single p with these restrictions states
   agreement on overlaps as well as the required gluing. p's own equation is
   over B, and its separated and finite-type predicates are explicit conclusions.
10. r is pinned by r followed by H inclusion = a.left.toImage. Its open immersion,
    quasi-compactness, schematic dominance and DenseRange assert the inclusion of
    V in H and both densities for that very inclusion. vU followed by U inclusion
    equals r followed by p; pointImage vU = Set.univ is surjectivity onto U in the
    existing point topology, with no sectionwise-surjectivity strengthening.
11. The final forall K, v, L, b includes the identity extension and every field
    extension. P's presheaf square is explicitly IsPullback over the field-valued
    image of v under p. c_i is a morphism over Spec L from its identity object,
    and its composite with w is exactly the base-changed ith coordinate of v.
    IsColimit (Cofan.mk P c) therefore specifies the labelled split fibre, not
    only an unlabelled isomorphism to an arbitrary disjoint union. Applying the
    clause with L=K and b=id gives the original fibre; the prescribed injections
    keep the same identification on every extension. K and L have no closure,
    finiteness or separability assumptions. Nonsplit arbitrary fibres of X are
    not claimed to split: this conclusion requires v in the distinct configuration.
12. Empty U, A=0, nonreduced A, d=1 and m=0 are all admitted by these exact binders.
    Empty V has no field-valued input v and the last clause is vacuous there;
    its image, the canonical schematic closure, and H are empty as required.
    None of the definitions has postponed data. The theorem's one sorry remains
    the whole proof, with the eleven-step natural-language proof in its docstring.

Findings and repairs: the mathematical clauses match the node and the construction
portion of Tag 089J; no signature change is warranted. H2 was a real dependency-owner
mismatch: the old packet cited an enlarged-site comparison theorem only to obtain
schemeSpace. I replaced that id by def-trf-scheme-algebraic-space and replaced the
aggregate SpaceCotangentRingMap import by the definition's recorded module,
EnlargedEtaleRingedSite. H11 was a missing reading: this section replaces the old
no-reading paragraph with the actual checks above. The cosmetic header point was
checked against the retained sandbox: it already contains one copyright block and
one module command; the repaired file keeps exactly one of each. No duplicate block
is delivered. The original theorem signature agrees byte-for-byte with lean.statement
and is preserved through this repair. The current main node has no lean record, so the
packet is rebuilt from that node, retaining every base field other than lean and the
three allowed added definition dependencies. deliver2.py refreshes the live delivery
base before its dry run and push.
