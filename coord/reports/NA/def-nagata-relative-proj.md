## Worker report

The module `Sheaf.AlgebraicGeometry.RelativeProjData` defines the construction datum
`AlgebraicGeometry.RelativeProjData`, together with its input representation
`RelativeProjAlgebra`, actual local section rings, induced gradings, local Proj schemes,
canonical structural and transition maps, and the glued scheme and morphism. It asserts
no existence or cover independence of the construction datum. Those remain the separate
node `lemma-nagata-relative-proj-exists`. The item JSON changes only in `lean`.

Clause-by-clause correspondence:

- A scheme X: the explicit binder `X : Scheme.{u}`. No separation, Noetherian,
  nonemptiness, finiteness, or degree-zero-equality assumption is present.
- A commutative unital graded algebra sheaf: `RelativeProjAlgebra.piece : ℕ → X.Modules`
  and `graded : GradedSheafAlgebra piece` reuse the recorded homogeneous-sheaf structure.
  `algebra : QuasiCoherentAlgebra X` is the total commutative unital algebra sheaf.
  `decomposition : (∐ piece) ≅ algebra.obj.toModule` identifies its underlying module
  with the sheaf direct sum, as the dependency definition prescribes. `mul_eq` and
  `unit_eq` identify the total algebra operations with those of `graded`.
  These are the representation of the input algebra, not additional mathematical
  restrictions: the source already says its underlying sheaf is the sum and that its
  operations are the extensions of the homogeneous operations. The arbitrary isomorphism
  allows either realization of that sheaf sum; the two compatibility equations identify
  precisely the same algebra, rather than an unrelated algebra on its underlying module.
- Quasi-coherence as an algebra sheaf: `algebra : QuasiCoherentAlgebra X` uses
  `Scheme.IsQuasiCoherentAlgebra`, namely quasi-coherence of `algebra.obj.toModule`.
- For every affine open V: every local definition binds `V : X.affineOpens`.
  `sections V` is literally `algebra.obj.right.obj.obj (op V.1)`, the section ring C_V.
  The R_V in `unitZero` is literally `Γ(X, V.1)`.
- Induced grading: `sectionGrade V n` is the image of the homogeneous inclusion
  `Sigma.ι piece n ≫ decomposition.hom` on sections. `sectionGradedRing` uses the
  named multiplication, unit, and internal-direct-sum proof obligations. Affineness is
  essential in `sectionGrade_internal`: sections over a non-quasi-compact open need
  not commute with an infinite sheaf direct sum. We do not claim that here.
- P_V = Proj(C_V): `localProj V := Proj (sectionGrade V)`, using the existing Mathlib
  Proj scheme and the actual section ring, not an arbitrary ring or an affine substitute.
- p_V: `localBase V` is exactly `Proj.toSpecZero` followed by
  `Spec.map (CommRingCat.ofHom (unitZero V))` and `V.2.isoSpec.inv`. The unit homomorphism
  has codomain `sectionGrade V 0`; there is no requirement that it be an isomorphism.
- Choose an affine cover: the specified choice is the cover of all affine opens,
  `X.directedAffineCover`, explicitly permitted by the node. Its index is the full type
  `X.affineOpens`, in the scheme universe. The construction does not depend on selecting
  a nonempty index family when X is empty.
- The local schemes and maps in gluing: `gluing.functor` and `gluing.natTrans` are
  identified with `localProj` and `localBase` by `localIso` and `local_over`.
- Overlap maps induced by restriction, including their standard-chart descriptions:
  `localTransition h := Proj.map (restriction h) (irrelevant_le h)`.
  `restriction h` is the actual algebra-sheaf restriction ring homomorphism with its
  degree-preservation proof. Mathlib's `Proj.map` is defined on homogeneous fractions by
  applying this homomorphism to numerator and denominator. Its `map_preimage_basicOpen`
  and `awayToSection_comp_appLE` in ProjectiveSpectrum/Functor implement the corresponding
  degree-zero homogeneous localization chart maps. On a principal affine restriction,
  quasi-coherence identifies this very section restriction with coefficientwise
  localization; no extra independently chosen chart map can occur in this definition.
  `local_transition` pins every gluing transition to that canonical map.
- Inverse-image overlaps and identity, inverse, triple-overlap compatibility:
  `gluing : Scheme.Cover.RelativeGluingData X.directedAffineCover` is exactly the
  dependency's relative scheme-gluing representation. Its `equifibered` property says
  each local transition identifies its source with the inverse image of the smaller
  affine open, and its functor fields include identity and composition equalities.
  For V_i∩V_j one uses all affine refinements W⊆V_i∩V_j: the two equifibered squares
  identify the common pieces, and the functor identity/composition equations identify
  their common further restrictions. The resulting overlap identifications therefore
  include the identity, inverse, and cocycle equalities in precisely this basis encoding.
  No assertion that V_i∩V_j is affine is made.
- Glue using relative scheme gluing: `RelativeProjData.proj := D.gluing.glued` and
  `RelativeProjData.π := D.gluing.toBase`. The output scheme is the existing gluing
  construction itself, not an unspecified scheme with no relationship to the gluing.
- Every affine restriction isomorphism i_V: `restrictionIso V` has source
  `(gluing.toBase ⁻¹ᵁ V.1).toScheme` and target `localProj V`. `restriction_ι` identifies
  it with the actual inclusion into the glued scheme, using `localIso` and the colimit
  inclusion. `restriction_over` says exactly that it commutes with the maps to V,
  expressed after V's monomorphism into X (equivalently an equality over V).
- For affine W⊆V: `restriction_compatibility V W h` is verbatim the composite
  `i_W.inv ≫ homOfLE (π.preimage_mono h) ≫ i_V.hom = localTransition h`.
- Existence and independence are separate: `RelativeProjData` is a type of specified
  data; neither a value of this type nor its existence nor uniqueness is assumed.
  The named helper theorems only discharge well-definedness of the already specified
  input section grading and canonical local maps. They do not supply a gluing datum.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Spec`,
  `Spec.map` (scheme and affine-spectrum nodes).
- `Sheaf.AlgebraicGeometry.GradedSheafStructures`: `AlgebraicGeometry.GradedSheafAlgebra`,
  including all fields and their homogeneous operation signatures.
- `Sheaf.AlgebraicGeometry.QuasiCoherentAlgebra`: `QuasiCoherentAlgebra`,
  `Scheme.IsQuasiCoherentAlgebra`; underlying `Scheme.CommAlgebraSheaf.toModule` was also
  read in `Sheaf.AlgebraicGeometry.CommAlgebraSheaf`.
- `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme`: `AlgebraicGeometry.Proj`;
  `ProjectiveSpectrum.Basic`: `Proj.toSpecZero`; `ProjectiveSpectrum.Functor`: `Proj.map`.
- `Mathlib.AlgebraicGeometry.RelativeGluing`: `Scheme.Cover.RelativeGluingData`,
  `.glued`, `.toBase`, and the equifibered interface; `Cover.Directed`:
  `Scheme.directedAffineCover`. This is the dependency's recorded mathlib_match,
  specialized as that record instructs.
- `Mathlib.AlgebraicGeometry.AffineScheme`: `IsAffineOpen.isoSpec`.

Six named `sorry` obligations, all recorded in the item's `lean.declarations` and each
with its source and natural-language proof in its docstring:
`RelativeProjAlgebra.sectionGrade_one`, `.sectionGrade_mul`, `.sectionGrade_internal`,
`.restriction_mem`, `.irrelevant_le`, `.unit_mem`.
All are well-definedness obligations for this same definition node, not new notions.
The only data obtained from an unproved theorem is `chooseDecomposition` of the proven-
bijective recomposition map: it is its uniquely determined inverse, explicitly allowed
by AGENTS.md §5. `DirectSum.Decomposition` is itself a subsingleton. No ring, sheaf,
scheme, transition, or gluing datum is chosen from an unrestricted existence theorem.

Edge cases checked by inspecting the signatures and formulas:
empty X and its affine basis; the zero algebra (Proj empty); positive degrees all zero
(Proj empty); arbitrary nonzero degree-zero algebra with no identification A_0=O_X;
infinitely many nonzero homogeneous pieces (direct sum is a sheaf coproduct);
non-affine intersections and non-separated X (all affine refinements are used);
nonprincipal affine subopens (use the actual restriction and base change of pieces);
identity inclusions (functor identity); three nested inclusions (functor composition);
arbitrary scheme universe u. No finite-generation or degree-one-generation condition.

Searches for an existing notion and declaration:

- `msearch.py ... leanfinder "Relative Proj of a quasi-coherent graded algebra sheaf
  gluing affine projective spectra"`: 8 hits, including `AlgebraicGeometry.Proj`,
  `Proj.toSpecZero`, `Proj.fromOfGlobalSections`, `Proj.awayι`, `Proj.basicOpenToSpec`,
  `ProjectiveSpectrum` and `projIsoSpec`. These are single-ring Proj APIs, not the
  construction datum for an algebra sheaf.
- `msearch.py ... loogle "AlgebraicGeometry.Proj, GradedAlgebraData.relProj"`: 0 hits,
  unknown identifier `GradedAlgebraData.relProj`.
- `msearch.py ... grep "RelativeProj|relProj|GradedAlgebraData" AlgebraicGeometry`:
  0 hits in Mathlib.
- `msearch.py ... leansearch "Relative projective spectrum of a graded quasi coherent
  algebra sheaf on a scheme"`: service unavailable, Internal Server Error; unavailable
  search recorded, with the other searches used.
- `rg` in upstream WeilConjectures and project `lean/Sheaf` for relative Proj, relProj,
  the node id, and the new names: no reusable declaration of this notion. Upstream's
  compactification projective-space embeddings are specialized and do not define
  relative Proj for a general graded algebra sheaf. The node's audit lists old
  `WeilConjectures.AlgebraicGeometry.RelativeProj.Basic` and `GradedAlgebraData` files,
  but these files and their declarations are absent from the supplied source checkout.
  No declaration is reused merely on the strength of that stale name index.
- New full declaration names were searched in Mathlib, upstream, and project Sheaf:
  no collisions found. No new nodes or dependency replacements were needed.

Validation: `scompile.py NA def-nagata-relative-proj <module>` passed on the server in
3.2 seconds, nice 19, two threads, 60-second per-file limit, with no errors or warnings.
No local Lean invocation or library build was run. No statement correction or
STATEMENT-DISPUTED flag is needed.

## Second reading by NA

Independent reading of the repository node, the complete delivered module, all six
statement dependencies, and the source passages. The source is the blueprint's
`def-nagata-relative-proj.md`, order 12. I also read Stacks `constructions.tex`,
Situation `situation-relative-proj`, Lemmas `lemma-proj-inclusion`,
`lemma-transitive-proj`, `lemma-glue-relative-proj`, and the relative-gluing
Lemma 01LH. The standing source assumptions are precisely a scheme and a
quasi-coherent graded algebra; they impose neither a degree-zero identification
nor finite generation nor separation. No statement correction is present or needed.

Object/hypothesis/conclusion checklist, recorded independently:

1. An arbitrary scheme X: `RelativeProjAlgebra (X : Scheme.{u})`, followed by
   `RelativeProjData {X : Scheme.{u}} (A : RelativeProjAlgebra X)`. PASS.
2. A commutative unital N-graded O_X-algebra with sheaf direct-sum underlying module:
   `piece`, `graded : GradedSheafAlgebra piece`, `algebra`, `decomposition`,
   `mul_eq`, `unit_eq`. I read the dependency's homogeneous bilinear operations,
   naturality, associative/commutative/unit laws, and its direct-sum convention.
   The two compatibility equations tie those operations to the actual total ring
   sheaf. They do not assume an unrelated multiplication or a stronger grading.
   PASS; this packages exactly the input rather than a replacement notion.
3. Quasi-coherence of that total algebra: `algebra : QuasiCoherentAlgebra X`.
   I read `Scheme.IsQuasiCoherentAlgebra`, the full-subcategory abbreviation, and
   `Scheme.CommAlgebraSheaf.toModule`. This is quasi-coherence of the underlying
   module of the same ring sheaf. No Noetherian or finite-presentation instance.
   PASS.
4. For every affine V, R_V and the genuinely induced graded C_V:
   `V : X.affineOpens`, `sections V`, `sectionGrade V n`, `sectionGradedRing V`.
   The subgroup is the image of the homogeneous inclusion on V-sections. The
   internal-direct-sum obligation is restricted to affine opens, where the
   quasi-coherent module/sections equivalence applies. PASS.
5. P_V and p_V: `localProj V := Proj (A.sectionGrade V)` and `localBase V`.
   I checked the dependency node's `AlgebraicGeometry.Proj`, Mathlib's
   `Proj.toSpecZero`, and `Spec.map` signatures and directions. The latter is
   applied to `unitZero V : Γ(X,V.1) →+* A.sectionGrade V 0`, then followed by
   `V.2.isoSpec.inv`. No A_0 = O_X or isomorphism of these rings is assumed.
   PASS; the models are schemes, not asserted affine schemes.
6. A specified affine cover: `X.directedAffineCover`, whose index, object and
   structural map are respectively all affine opens, their open subschemes, and
   inclusions. I opened its definition and LocallyDirected instance. The node
   explicitly permits this choice. PASS.
7. Local models and maps over the cover: `localIso`, `local_over`. Both use the
   exact `localProj` and `localBase` just checked. PASS.
8. Restriction-induced overlaps and homogeneous localization charts:
   `restriction h` has the actual ring-sheaf restriction as `toRingHom`;
   `localTransition h := Proj.map (A.restriction h) (A.irrelevant_le h)`;
   `local_transition` identifies the gluing functor map with this morphism.
   I read Mathlib Functor's `sheafedSpaceMap`, `map`,
   `map_preimage_basicOpen`, and `awayToSection_comp_appLE`: the chart map is
   exactly `HomogeneousLocalization.Away.map` of that restriction. For principal
   affine restrictions this is coefficientwise localization by quasi-coherence,
   not an independently specified map. PASS.
9. Inverse-image opens, identity/inverse/cocycle compatibility: the dependency's
   `Scheme.Cover.RelativeGluingData` has a functor, a natural transformation,
   and `equifibered : natTrans.Equifibered`. I read this structure and its
   pullback interface. The pullback squares give the inverse-image opens; functor
   identity/composition give compatible restrictions. For two unrelated affine
   opens their intersection is covered by smaller affine opens; composing the
   identifications through these common pullbacks gives the overlap isomorphisms,
   inverses, and triple cocycles. No affine-intersection hypothesis is hidden.
   PASS; this is the dependency node's recorded basis encoding of 01LH.
10. Glue using that construction, with resulting scheme and structural map:
    `RelativeProjData.proj := D.gluing.glued` and
    `RelativeProjData.π := D.gluing.toBase`. I checked `.glued` is the colimit
    and `.toBase` its induced map. These are constructions, not arbitrary output
    objects. PASS.
11. For every affine V, i_V over V: `restrictionIso V` has source the actual
    `gluing.toBase` preimage of V and target `A.localProj V`.
    `restriction_ι` identifies it with the colimit chart, and `restriction_over`
    expresses its being over V after the mono V → X. PASS; no existence or cover
    independence of this type of specified data is postulated.
12. For W ≤ V the exact composite required by the node:
    `restriction_compatibility V W h` is i_W.inv, the actual inclusion of
    preimage opens, then i_V.hom, equal to the same `localTransition h`. PASS.

Edge cases: empty schemes are permitted and the affine-basis cover requires no
Nonempty instance; the zero algebra and an algebra supported only in degree zero
are allowed (their local Proj can be empty); degree zero is present without being
identified with O_X; arbitrary characteristic, infinitely many homogeneous pieces,
nonprincipal affine subopens, and non-affine intersections in nonseparated schemes
are not excluded. All scheme/module/section carriers use the same arbitrary u,
and the indexing affine opens are in the scheme universe. There is no independent
smaller test universe or field restriction. Identity and nested inclusions are
included by the universal h binders and functor laws.

Independent duplicate searches (including different terminology from the worker):

- LeanFinder: `relative Proj graded algebra sheaf` and `projectivization graded
  quasi coherent sheaf over scheme`: only absolute ring-level Proj, its sheaf and
  chart API, and `Proj.fromOfGlobalSections`; no general sheaf-relative construction.
- Loogle: `RelativeProjData`: unknown identifier, zero hits in the search service.
- Search wrapper grep: `projectivization|projectivisation|graded.*sheaf|relative.*homogeneous`
  in AlgebraicGeometry: only the ring-level Proj sheaf comment.
- LeanSearch: `glue projective spectra over affine open subsets`: service unavailable
  (Internal Server Error), recorded without treating it as negative evidence.
- Direct rg of Mathlib, upstream WeilConjectures, and project lean/Sheaf for
  RelativeProj/relProj/GradedAlgebraData and the terminology above: no reusable
  relative-Proj datum. Upstream has relative projective space and absolute graded
  module sheaves; these are different notions. The old RelativeProj audit paths
  still have no matching source files in the supplied checkout.

H4/H12/H13: no duplicate found, no new definition nodes or replacement dependency
modules are needed. The input presentation uses the recorded homogeneous sheaf
structure and recorded quasi-coherent algebra, rather than private replacements.
H5/H6: all six theorem proofs are `sorry` and each has its source and natural-language
proof. The section grading uses the uniquely determined decomposition of the
recomposition map, not a free choice of algebraic data: Mathlib declares
`Subsingleton (DirectSum.Decomposition ...)`. Other data are explicit formulas or
fields of the construction datum. No existence of that datum is inferred from a
sorry. The node has no proof steps requiring additional proof imports.
H8/H9: module and declaration docstrings name the source and blueprint; all variables
and u are bound, imports serve the constructions, and no private declaration or
file-local notation/instance is used. The node's lean.statement is verbatim the
main structure signature in the file.

Mismatches found: none. Changes: appended this independent reading only; the Lean
and node were left unchanged. Server validation with scompile.py passed in 3.1 s,
nice 19, two threads, 60-second per-file limit, with no errors or warnings.
