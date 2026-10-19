## Worker report

Item: lem-sf-proetale-tensor-composition-unit. Group Q137. Stage 2 only.

The module `Sheaf.AlgebraicGeometry.ProEtaleTensorCompositionUnit` states
`AlgebraicGeometry.Scheme.proEtale_tensor_composition_unit`, with proof `sorry`.
It also defines two real-data section expressions belonging to this comparison:
`proEtalePullbackTensorGenerator` and `proEtalePullbackTensorScalar`.
These helpers do not introduce alternative inverse images, module categories, tensor
products, coefficient maps, adjunctions, or composition comparisons.
There is exactly one postponed theorem in the delivered module. Its docstring carries
all four steps of the DAG proof, including balancing in both rings and uniqueness.

### Every hypothesis and construction

- Schemes V, W, Z and arbitrary morphisms h : Z → W and k : W → V are the first
  binders, with `Scheme.{u}` and no geometric-property instances.
- The small pro-etale sites and their actual base-change functors are the published
  `ProEt.topology` and `proEtaleBaseChange`. They retain the object universe u+1,
  morphism universe u, and coefficient universe u+1. The module construction uses
  the dependency's AsSmall model and transport back, imposing no equality between
  these site universes and discarding no objects.
- The arbitrary commutative ring sheaves are the three binders `R_V`, `R_W`, `R_Z`
  of type `Sheaf (ProEt.topology _) CommRingCat.{u+1}`. No finiteness, topology on
  coefficients, constant-coefficient restriction, or nonzero-ring assumption occurs.
- The specified ring-sheaf isomorphisms are `c_k` and `c_h`, using exactly the
  recorded `proEtaleSheafInverseImage`, not independent ring maps.
- The canonical inverse-image composition comparison on rings is the already
  published `proEtaleRingInverseImageComp h k`. Its direction is composite inverse
  image → iterated inverse image, so it is the paper's a inverse. Its definition
  is the mate of the actual fibre-product-pasting right comparison under the
  specified sheaf adjunctions. This is the adjunction-normalized comparison of
  the site-composition node, transported along the canonical fibre products.
- `c_hk` and `hc_hk` merely name the prescribed composite coefficient isomorphism:
  `c_hk = (proEtaleRingInverseImageComp h k).app R_V ≪≫
  (proEtaleSheafInverseImage h CommRingCat).mapIso c_k ≪≫ c_h`.
  Thus they implement exactly the node's “set c_(kh) = ...”, without allowing an
  independent choice or adding a mathematical restriction. For every input c_k,c_h,
  that expression itself supplies c_hk with equality rfl. There is no statement let.
- The module operations in all binders and conclusions are the published
  `proEtaleRingModulePullback` and `proEtaleRingModuleDirectImage` on
  `proEtaleRingModules`. Pullback's actual object definition is the sheaf tensor
  extension `SheafOfModules.changeOfRings c.hom` of `proEtaleModuleInverseImage`.
  Direct image is sectionwise base-change restriction with the action through
  `proEtaleRingDirectImageMap`. No arbitrary functor is substituted.
- Every adjunction used is `proEtaleRingModuleAdjunction`: the dependency selects
  it from its UNIQUE tensor-unit normalization, using the model-site transpose
  after the sheafification of 1 ⊗ m. We do not existentially choose adjunctions.

### Every conclusion clause

1. `d` has type `(kh)_* ≅ h_* ⋙ k_*`, which in Lean functor order is the paper's
   `(kh)_* ≅ k_*h_*`. Its first conjunct quantifies every module N, every test
   object U, and every section m, requiring its component to be precisely
   `N.val.map ((Over.pullbackComp h k).inv.app U).op m`.
   `Over.pullbackComp.hom` goes from composite base change to iterated base change,
   so its inverse is the paper's q : B_h B_k U → B_(kh) U. Contravariant restriction
   along this q has exactly the stated direction. A natural isomorphism consists
   of linear sheaf maps with mutual inverses, so linearity, naturality and the
   inverse restriction map are included rather than assumed separately.
2. `t` has type `k^* ⋙ h^* ≅ (kh)^*`. The second conjunct explicitly gives the
   forward tensor formula. It quantifies EVERY U in V.ProEt, T in W.ProEt, P in
   Z.ProEt, indexing arrow p : T → B_k U, indexing arrow q : P → B_h T, section
   m of M(U), scalar a of R_W(T), and scalar b of R_Z(P).
   The left side applies t to the nested `proEtalePullbackTensorGenerator`s,
   representing `(m ⊗ a) ⊗ b`. The right side is the composite-pullback generator
   indexed by `q ≫ B_h.map p ≫ (Over.pullbackComp h k).inv.app U`, with final
   scalar `proEtalePullbackTensorScalar h ... q a * b`. The scalar helper is
   restriction of rho_h(a), precisely c_h of the inverse-image generator of a.
   Thus this is the required multiplication formula including a on the
   inverse-image factor, not just an unspecified natural isomorphism.
3. The third conjunct explicitly specifies t.inv on every composite-pullback
   generator, for arbitrary p : P → B_(kh) U, m in M(U), and b in R_Z(P).
   Its output is the outer generator with index `p ≫ pullbackComp.hom.app U`
   applied to the inner generator with scalar 1. This is `(m ⊗ 1) ⊗ b`, using
   the inverse composition comparison. Because t is a natural isomorphism,
   both inverse identities hold as module-sheaf maps and naturally in M.
4. The fourth conjunct is exactly the displayed unit equation, for every M:
   eta_k followed by k_* applied to eta_h at k^*M, followed by k_*h_* applied
   to t_M, equals eta_(kh) followed by d at (kh)^*M. Lean's `≫` reads these
   compositions in application order, opposite to the paper's right-to-left ∘.
5. The last conjunct quantifies ALL natural transformations t', not just
   isomorphisms. If t' satisfies the same unit equation with d, then t'=t.hom.
   It uses `Adjunction.comp` for the composite unit. Its `comp_unit_app` is
   exactly the successive-unit expression in conjunct 4. This is the specified
   uniqueness under the conjugate-iso/unit-equation dependency.

### Why the indexed formulas retain arbitrary local tensor sections

The displayed formulas do not restrict m to global sections or a,b to constants.
`proEtalePullbackTensorGenerator f ... U T p m r` is r times the restriction
along p of the specified tensor-normalized unit applied to m. That unit is the
sheafification of the inverse-image coprojection followed by m ↦ m ⊗ 1.
Consequently these are the images of all pure-tensor generators in all indexing
coprojections of the sheafified Kan construction. Maps out of the colimit are
specified on all its coprojections; maps from its sheafification to a sheaf are
specified before sheafification; additive tensor maps are specified on pure tensors.
For the iterated construction the arbitrary p and q specify all iterated indices.
Local sections of the inverse image need not themselves be single generators:
linearity and sheafification extend the formulas to their local sums. For combining
indices of m and a, the finite-limit-preserving base change gives the usual common
refinements of the inverse-image index. The specified coefficient isomorphisms let
inverse-ring coefficients be absorbed in the final scalar. Thus the two clauses
are equivalent to the paper's formulas after its canonical inverse-image/tensor
identifications. The unit equation is asserted IN ADDITION to these generator
formulas, rather than being used as a replacement for them.

### Dependency declarations read and used

- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `AlgebraicGeometry.Scheme.proEtaleBaseChange`, `proEtaleSheafInverseImage`,
  `proEtaleSheafDirectImage`, `proEtaleSheafAdjunction`, `proEtaleSiteModel`,
  `proEtaleModelBaseChange`, `proEtaleModelRingUnit`, `proEtaleModuleInverseImage`.
  Read the complete source, including the model transport and its docstrings.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations` publicly imports
  `ProEtaleOperationsCanonicalAdjunction` and `ProEtaleOperations`, which provide
  the arbitrary R,S,c interfaces used here: `proEtaleRingModules`,
  `proEtaleRingDirectImageMap`, `proEtaleRingModulePullback`,
  `proEtaleRingModuleDirectImage`, `proEtaleRingModuleAdjunction` and its
  `proEtaleRingModuleAdjunction_existsUnique` normalization. Read all three sources.
  The finite/constant specializations reexported by this recorded dependency are
  not imposed on the present theorem.
- `Sheaf.CategoryTheory.SiteMorphismComposition`:
  `CategoryTheory.siteMorphism_composition`. Read both this full signature and
  docstring and the recorded WeilConjectures owner with `scompile.py --source`.
  The lean-only exact existing rebind is described below.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, its projections and lift. The site-object
  comparison is the existing `CategoryTheory.MorphismProperty.Over.pullbackComp`
  from Mathlib's OverAdjunction. Read its full signature, components and orientation.
- `Mathlib.CategoryTheory.Adjunction.Mates`:
  `CategoryTheory.unit_conjugateEquiv_symm`, `conjugateIsoEquiv`; read the unit
  equation and Hom correspondence used for the uniqueness clause.
- `Mathlib.CategoryTheory.Adjunction.Basic`:
  `CategoryTheory.Adjunction.comp`, `comp_unit_app`, `comp_counit_app`,
  `comp_homEquiv` and identity adjunction. Read their definitions and signatures.
- `Sheaf.CategoryTheory.SiteInverseImageTensor`:
  `CategoryTheory.siteInverseImage_tensor`, `siteInverseImage_tensor_coherence`.
  Read both complete signatures and proof docstrings. Retained as proof imports.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`: the recorded
  proof dependency def-pur-sheaf-tensor-product; its sectionwise tensor and
  sheafification interfaces underlie the balancing argument. Retained as a proof import.
- Added the already landed node `lem-weil-pbc-profinite-coefficient-inverse-image`
  to stmt_deps for its real-data helper
  `AlgebraicGeometry.Scheme.proEtaleRingInverseImageComp`, in
  `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`. Read the whole source.
  This helper has NO finite/profinite-ring hypotheses. Only this helper is used;
  the finite-tower theorem is not used to restrict the present coefficient sheaves.
  No dependency on a downstream module-pullback-composition theorem was introduced.

### Sources and edge cases

Read Stacks sites.tex at lemma-composition-morphisms-sites (03CB) and the following
composition definition (03CC), and sites-modules.tex at lemma-adjoint-push-pull-modules
(03D3) and lemma-tensor-product-pullback (03EL). Read the current main-20261015
blueprint def-pur-scheme-geometric-frobenius, especially its final compatibility
sentence and equation. The item is an auxiliary calculation, not a unit statement.

Checked the directions of q, a and d against the actual Over.pullbackComp definition.
Checked identity h or k (the same formulas with the canonical identity transports),
zero module M, zero coefficient rings, M=R_V, a=0, b=0, a=b=1, arbitrary indexing
arrows and empty scheme/test objects. The equations are linear and use no nonzero
or nonempty assumptions, no properness, flatness, finite type or characteristic.
The coefficient universes retain all sheaves in the stated larger universe.
The generator definitions have actual data, using the dependency's uniquely
normalized adjunction. All universes and variables are explicitly bound and
`autoImplicit false` is set; no file-local notation, private object or instance
occurs in the delivered module. No STATEMENT-DISPUTED or statement correction.

### Searches

The required launcher searches were run with group Q137 and the item id:

- leanfinder: `explicit tensor pullback composition of sheaves of modules preserves
  adjunction unit` → 8 hits, including SheafOfModules.pullbackComp,
  conjugateEquiv_pullbackComp_inv and single-pullback/free-module unit lemmas.
  None identifies the explicit pro-etale inverse-image/tensor comparison.
- loogle: `SheafOfModules.pullbackComp, CategoryTheory.unit_conjugateEquiv_symm`
  → 0 hits for that combined query.
- grep: `pullbackComp|conjugateEquiv|changeOfRings` in
  Algebra/Category/ModuleCat/Sheaf → 6 hits, including PullbackContinuous.lean
  pullbackComp and conjugateEquiv_pullbackComp_inv, and ChangeOfRings imports.
  Read PullbackContinuous.lean: pullback is chosen abstractly as a left adjoint;
  the composition map is defined by conjugation, so it is not this theorem.
- leansearch: `explicit proetale tensor pullback composition agrees with adjunction unit`
  → 8 hits, mainly ChosenPullbacksAlong.unit_pullbackComp_hom and categorical
  pullback-adjunction lemmas, no explicit pro-etale tensor normalization theorem.
- rg in the named older WeilConjectures checkout: searched the item id (no hit),
  `tensor.*[Cc]omposition|[Cc]omposition.*tensor|proEtaleRingModule.*Comp` (no exact
  theorem there). The corresponding side-library search found derived and constant
  composition statements, which do not include both present explicit formulas.
- rg in lean/Sheaf and in the pinned Mathlib/source/name index for
  `tensor_composition_unit|PullbackTensorGenerator|PullbackTensorScalar`: no name
  collision. Read ProEtaleDerivedPullbackComposition and
  ProEtaleCanonicalPullbackComposition: these normalize an abstract comparison
  and derived/K-flat consequences; neither states the present explicit-generator
  normalization with its specified adjunctions. No existing-match delivery is possible.

### Validation

The module was compiled using the prescribed scompile.py wrapper, never Lake or a
whole-library build. The first pass was clean for both sandbox and library names
(4.5 s and 3.7 s). A final pass includes the recorded tensor proof dependency.
Only the named theorem has `sorry`; both helper definitions are real expressions.
Every Lean line is at most 100 characters. The signature in lean.statement is
extracted verbatim from the final theorem keyword through the text before `:=`.

## Dependency modules

Exact existing-interface repair under §1(B), no new dependency module:
`lem-weil-pbc-site-morphism-composition` changes only `lean`, rebinding the same
`CategoryTheory.siteMorphism_composition` to
`Sheaf.CategoryTheory.SiteMorphismComposition` with existing=true. Its old recorded
WeilConjectures owner declares the same name as that Sheaf owner, which the mandatory
ProEtaleInverseImage import closure already contains. The Sheaf source and server
source of the old owner have the same statement and proof docstring. Using the
single published Sheaf owner avoids a duplicate declaration and does not replace
or specialize the dependency. The record's note explains the reason and exact match.

## New nodes

None. The only stmt_deps addition is the already landed profinite-inverse-image
node for its unrestricted ring inverse-image composition helper. The two section
expressions are helpers of this item's construction, recorded in lean.declarations,
not independent new mathematical notions.

## Second reading by Q137

Independent maintainer second reading, 2026-10-17, of immutable delivery
10ca85cdcef914c4a7ff527a0cbaff4869d64de8. This reader neither wrote nor previously
second-read this delivery. The required heading is retained; this is the independent
maintainer reading requested for Q137, not a claim that a second Q137 worker reviewed it.

I read the item and all eight statement-dependency records from the snapshot, the
complete delivered Lean file and worker report, and the exact dependency declarations
in the read-only Q137 clone and pinned Mathlib. I read check-brief2.md in full,
brief-stage2.md, delivery-errors H, and pefw-upstream-framework.md.

Hypotheses and constructions:

- Arbitrary schemes V,W,Z and arbitrary h:Z→W, k:W→V are exactly the first binders.
  No properness, flatness, weak-etaleness of h or k, characteristic, or finiteness
  assumption is introduced. Scheme.{u}, original ProEt sites (objects u+1, Homs u),
  and coefficients/modules in u+1 follow the recorded convention.
- R_V,R_W,R_Z are arbitrary commutative ring sheaves, not constant or finite rings.
  c_k,c_h are the specified inverse-image ring isomorphisms. c_hk together with
  hc_hk only names their prescribed composite: substituting the displayed composite
  always supplies this parameter, so this introduces no extra restriction.
- proEtaleBaseChange and proEtaleSheafInverseImage are the recorded constructions:
  actual weakly-etale slice base change and sheafified left Kan extension.
  proEtaleModuleInverseImage transports through AsSmall and back without discarding
  objects; proEtaleRingModulePullback applies actual sheafified changeOfRings.
  The published module direct image has scalar action through the adjunct of c.
- proEtaleRingInverseImageComp is an actual mate of fibre-product pasting, not a
  chosen arbitrary map. Its direction is composite inverse image to iterated inverse
  image, the inverse of the node's a. It has no finite/profinite hypothesis.
  The added, already landed dependency is therefore appropriate even though its
  main theorem concerns finite coefficient towers.
- proEtaleRingModuleAdjunction is selected from existsUnique with an explicit
  tensor-unit transpose normalization. This determines the data, so neither its
  use in the generator helper nor the helper itself is hollow. The two delivered
  helpers are real expressions: scalar multiplication of a restricted unit image,
  and restriction of the adjunct coefficient map.

Conclusions, matched clause by clause:

1. d is a natural module isomorphism from composite direct image to iterated direct
   image. The first conjunct specifies its component on every section, exactly
   restriction along pullbackComp.inv. Mathlib OverAdjunction.lean:116 defines
   pullbackComp.hom from composite base change to iterated base change, making its
   inverse precisely the node's q. Linearity and inverse identities are supplied
   by the type of d, not an unrecorded assumption.
2. t is a natural module isomorphism from iterated pullback to composite pullback.
   The second conjunct specifies (m tensor a) tensor b ↦ m tensor c_h(a)b on all
   U,T,P,p,q,m,a,b. The resulting composite index is q followed by B_h(p) followed
   by pullbackComp.inv, with the correct direction.
3. The third conjunct specifies t.inv by inserting intermediate scalar 1, with
   index p followed by pullbackComp.hom. These are genuine tensor generators:
   the normalized unit supplies the inverse-image coprojection tensor 1;
   restriction and scalar multiplication give all indexed pure tensors. Colimit
   coprojections, additivity and sheafification extend these identities to all
   local sections. In the iterated construction the independent p,q and arbitrary
   intermediate scalar cover the iterated generators; finite limits give common
   refinements. No global-section or constant-scalar restriction occurs.
4. The fourth conjunct is exactly the displayed composite-unit equation, with
   Lean's application-order composition. The right side uses d at composite
   pullback M. Mathlib Adjunction.comp_unit_app:575 confirms the successive-unit
   expression on the left.
5. The last conjunct proves uniqueness among every natural transformation t',
   not merely among isomorphisms. unit_conjugateEquiv_symm:311 and the adjunction
   Hom bijection give exactly this orientation and characterization.

Sources and proof plan:

- Read sites-modules.tex:989–1129, especially 03D3 at label
  lemma-adjoint-push-pull-modules:1044, with its surrounding topos hypotheses and
  the tensor/restriction adjunction. Read 03EL at
  lemma-tensor-product-pullback:3649, including the bilinear Hom argument.
- Read sites.tex:2764–2801, 03CB and 03CC: continuity, inverse-image comparison
  by adjoint uniqueness, and composite direct image. Read categories.tex:3542–3616,
  0B65 and 0DV0, for mate characterization and composite adjunctions.
- Read the cited blueprint def-pur-scheme-geometric-frobenius final compatibility
  equation. This item is the auxiliary ordinary tensor calculation, not a change
  to that blueprint or to a target statement.
- The theorem docstring records all four DAG proof steps: fibre-product pasting;
  both balancing checks and both inverse identities; coefficient-action/unit
  compatibility; sectionwise unit calculation and uniqueness. I checked the
  A-balancing using beta(alpha(r)), outer B-balancing, and insertion of 1.
  None requires invertibility of elements or a nonzero ring.

Dependency repair and duplication checks:

The only dependency-record change is the lean-only rebind of
lem-weil-pbc-site-morphism-composition to its existing Sheaf owner. I read that
owner in full and fetched the old WeilConjectures owner with scompile.py --source.
Their theorem signatures and mathematical proof docstrings agree. The Sheaf owner
is already imported by the required inverse-image closure; retaining both owners
would duplicate CategoryTheory.siteMorphism_composition. This is a justified §1(B)
repair with a concrete lean.note. The retained legacy statement text agrees with
the existing declaration modulo whitespace, as checked by the merge tool.

I independently searched the Q137 Sheaf and WeilConjectures trees, the older source
WeilConjectures tree, and pinned Mathlib for pullbackComp, conjugateEquiv,
proEtaleRingModule composition, tensor-composition and the new helper names.
Read Mathlib Sheaf/PullbackContinuous.lean:43–76,155–182 and the project's
ProEtaleCanonicalPullbackComposition. The former is an abstract chosen-adjoint
comparison; the latter normalizes an ordinary/derived comparison but does not
state the explicit two generator formulas here. Neither duplicates this statement.
The worker report also records LeanSearch, LeanFinder, Loogle and grep searches.
No name collision or missing prerequisite construction was found. No §1(C)
statement correction or citer audit is needed; the source statement is unchanged.

Edge cases and gates:

Identity h or k retains the canonical fibre-product transports, rather than
assuming strict identity base change. Zero modules, zero rings, empty schemes
and test objects, m=0, a=0, b=0, and a=b=1 are included; no nonempty/nonzero
instance is bound. There is no extra index-set hypothesis. The sole universe u
is explicit; autoImplicit is false and the per-file compiler accepts all binders.
No universe equality or pro-etale substitute was introduced. Both helpers have
source/blueprint docstrings and real data; the single theorem has only sorry as
its proof. The module docstring has source and blueprint. Maximum line length
is 90. Imports provide signature declarations or recorded proof dependencies.
The item's lean.statement is byte-for-byte the theorem signature before :=.
Comparison with the read-only group-clone nodes shows only the item's lean and
stmt_deps, and the repaired dependency's lean, changed. No new nodes or modules
are concealed in the delivery.

Compiler evidence and correction:

I reran the immutable file with:
python3 /home/ubuntu/weil-launcher-nt/scompile.py Q137
lem-sf-proetale-tensor-composition-unit <snapshot absolute path>/lean/Sheaf/
AlgebraicGeometry/ProEtaleTensorCompositionUnit.lean
The wrapper exited 0: sandbox Sheaf/Stage2/Sandbox0.lean passed in 7.5 s;
library Sheaf/AlgebraicGeometry/ProEtaleTensorCompositionUnit.lean passed in 19.7 s.
There were no errors or warnings. The installed wrapper now delegates to the
server side-overlay compiler (announcing server compilation), rather than the
older local-wrapper implementation described in check-brief2. Its reported private
artifact directory was /dev/shm/nt-tmp/nt-local-compile-a2d3j5co/.lbuild.
This confirms the worker's recorded clean per-file result against the available
current overlay. No global build, live Lean write, direct ssh, delivery command,
Git mutation, or project-clone edit was performed.

Finding H11 (and the substantive-section requirement of H1): the delivered
“Second reading by Q137” contained only a disclaimer, not a reading. This complete
replacement report preserves the Worker report verbatim and replaces that placeholder
with this independent reading. No mathematical or Lean correction is necessary.
