## Worker report

The module `Sheaf.AlgebraicGeometry.QcOpenFlatSectionDiagram` states
`AlgebraicGeometry.Scheme.qc_open_flat_section_diagram` with `sorry`. Its seven helper
definitions supply the actual ordinary open-section algebras, their restrictions, their
scalar tensors, pure tensors, tensor restrictions, and finite-intersection opens and
inclusions. All helper data are constructed explicitly. The only postponed proof is the
item theorem. Only the item's `lean` field changes; no statement correction is needed.

Hypothesis and clause correspondence:

- Commutative rings and their homomorphism are `{R T : CommRingCat.{u}} (r : R ⟶ T)`.
  The flatness hypothesis is exactly `[Flat (Spec.map r)]`.
- The scheme over Spec R is `{Y : Scheme.{u}} (f : Y ⟶ Spec R)` and its absolute
  quasi-separatedness is `[QuasiSeparatedSpace Y]`. No quasi-compactness of Y is assumed.
  Mathlib's `quasiSeparatedSpace_iff_quasiSeparated` identifies this with the terminal
  structural morphism's quasi-separatedness; the equivalent formulation over the affine
  base also follows from `quasiSeparated_iff_quasiSeparatedSpace`.
- The arbitrary nonempty set-indexed family is `{I : Type v} [Nonempty I]
  (U : I → Y.Opens)`; `hU` asserts `IsCompact (U i : Set Y)` for each i.
  The index universe v is independent of u: the conclusion involves finite intersections,
  not a filtered colimit requiring a smallness bound on its indexing category.
- The nonempty finite subsets are `{F : Finset I // F.Nonempty}`, with the inherited
  inclusion order. The first two conjuncts assert their nonemptiness and directedness.
  `Directed (· ≤ ·) (fun F ↦ F)` is Lean's directed identity family, i.e. every pair of
  indices has a common upper bound.
- `qcFiniteIntersection U F` is the infimum of `U i` for `i : F.val`, exactly V_F.
  `qcFiniteIntersectionInclusion U h` is the canonical inclusion V_G into V_F for F ≤ G.
  Its underlying order proof restricts every member of G's intersection to each member of F.
- The actual X is `pullback f (Spec.map r)`, g is `pullback.fst f (Spec.map r)` and
  its map to Spec T is `pullback.snd f (Spec.map r)`. There are no arbitrary substitute
  schemes or maps. The third conjunct asserts absolute quasi-separatedness of X.
- The next conjunct asserts, for every F, compactness of V_F as a subset of Y,
  quasi-separatedness of its open subscheme, compactness of g⁻¹V_F as a subset of X,
  and quasi-separatedness of that open subscheme. These give exactly both qcqs clauses.
- `qcOpenSectionAlgebra f V` has underlying ring `Γ(Y,V)`. Its R-algebra map is
  `(ΓSpecIso R).inv ≫ f.appTop ≫ Y.presheaf.map (homOfLE le_top).op`.
  On X use the second pullback projection and T. Thus A_F and B_F have exactly the
  structural algebra actions in the node; none is an unspecified instance assumption.
- `qcOpenSectionRestriction f i` has ring map `Y.presheaf.map i.op`. Its scalar
  compatibility is established directly by presheaf composition. The tensor source
  `qcOpenSectionTensor r f V` is A_F tensor_R T with `rightAlgebra`, so T acts through
  `1 tensor t`; `qcOpenSectionTensorRestriction` tensors the restriction with `AlgHom.id R T`.
- The final existential gives a T-algebra isomorphism e F from that tensor to B_F for
  every F. Its first clause specifies its forward map on EVERY pure tensor a tensor t:
  it equals `(pullback.fst ...).app V_F a` times the structural image of t in B_F.
  This determines the canonical map by tensor-product universality, rather than choosing
  an unnormalized isomorphism. `@id` only aligns the identical underlying section carrier
  with its bundled algebra carrier; it does not change the section or map.
- Its last clause is exactly `(a_FG tensor 1) ≫ phi_G = phi_F ≫ b_FG` as an equality
  of T-algebra morphisms. Inverse-image inclusions are obtained by `Opens.map g.base`.
  This is the node's displayed equality in Lean's left-to-right composition convention.
  Ordinary restrictions satisfy identity and composition by the presheaf laws; the tensor
  maps inherit these laws. Thus this normalized family of component isomorphisms with all
  the stated squares is equivalently the requested isomorphism of directed diagrams.
- W_F is literally the inverse-image open with its inherited structure sheaf, and the
  map in the pure-tensor formula is literally g.app. The identification with
  V_F times Spec T is therefore the standard restricted pullback square; the docstring
  describes its proof from the fibre-product universal property, without substituting
  another sheaf or a freely supplied identification.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, `Spec.map`, `Scheme.ΓSpecIso`, `Scheme.Hom.app`, `appTop` and the structure
  presheaf. This realizes def-pc-scheme and def-weil-affine-spectrum.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat` and
  `isIso_pushoutSection_of_isQuasiSeparated_of_flat_right` (the recorded degree-zero
  input lem-weil-pbc-flat-base-change-global-sections-qcqs). Read its complete cartesian
  square, affine-open, compact-open and quasi-separated-open hypotheses.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`: `QuasiSeparated`,
  `quasiSeparatedSpace_iff_quasiSeparated`, `quasiSeparatedSpace_iff_forall_affineOpens`,
  and `Scheme.quasiSeparatedSpace_of_isOpenCover`. These are the exact interfaces recorded
  for def-weil-quasi-separated-morphism and the affine-cover criterion.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` (publicly available through
  Flat's imports): `pullback`, `pullback.fst`, `pullback.snd`, and the universal property;
  `Mathlib.AlgebraicGeometry.Pullbacks` supplies scheme pullbacks. These use the recorded
  def-pc-fibre-product, not a private fibre-product construction.
- `Mathlib.Algebra.Algebra.Hom`: `AlgHom`, used through `CommAlgCat` morphisms, for the
  algebra-hom portion of def-weil-pbc-algebra-hom-quotient. Its quotient/ideal clauses are
  not needed by this item. The node's `mathlib_match` is the usable interface; it need
  not receive an extra lean record.
- `Mathlib.RingTheory.TensorProduct.Basic` and `.Maps`: the recorded
  `Algebra.TensorProduct.instCommRing`, `tmul_mul_tmul`, `includeLeft`, `includeRight`,
  `productMap`, `productMap_apply_tmul`, `ext`, together with `rightAlgebra` and `map`.
  These provide the tensor algebra and its universal property. The final theorem fixes
  the universal map by its pure-tensor formula, avoiding any additional postponed theorem.
- Proof-only imports retain the nodes' recorded Mathlib interfaces: `Morphisms.Affine`
  (`isAffineHom_of_isAffine`, `isAffineHom_isStableUnderBaseChange`, the quasi-compactness
  instance), `Morphisms.Separated` (`IsSeparated.of_isAffineHom`),
  `Morphisms.FinitePresentation`, and `AlgebraicGeometry.Limits` (finite affine coproducts).
  Quasi-separated and quasi-compact permanence and open-immersion base change are in
  the imported Mathlib dependency closures. No upstream/project dependency was redefined.

Edge cases checked before and after drafting:

- I may be any nonempty type, including a singleton or an infinite family with repeated
  opens. F is always nonempty, so no empty infimum introduces an unintended V_F = Y
  that could fail compactness. The union of two admissible finite subsets remains admissible.
- Opens U_i and their finite intersections may be empty; no Nonempty condition is imposed
  on their points. Empty Y and X are permitted. Their section rings are zero rings, which
  CommRingCat and CommAlgCat allow, and the tensor/isomorphism formulation remains valid.
- R or T may be zero rings; there are no domain, characteristic or nontriviality hypotheses.
- Equality F = G and identity base change are included; restriction is the actual presheaf
  map and the formula fixes the canonical identity-base comparison.
- No covering hypothesis on U and no affine hypothesis on Y or V_F was introduced.

Searches for an existing full declaration, 2026-10-22:

- `msearch.py ... leanfinder "Flat base change global section tensor isomorphisms compatible
  with restrictions on finite intersections of quasi compact opens"`: eight hits, including
  `Flat.instResLE`, structure-sheaf composition, `pullbackSpecIso_hom_base`, and sheaf gluing;
  none states this refined directed-diagram theorem.
- `msearch.py ... loogle "AlgebraicGeometry.Flat, AlgebraicGeometry.Scheme.Hom"`: zero hits.
- `msearch.py ... grep "pushoutSection|tensor.*[Ss]ection" AlgebraicGeometry`: eight hits;
  Flat.lean gives the component isomorphism, not its indexed restriction squares.
- `msearch.py ... leansearch "Flat affine base change of structure sheaf sections on finite
  intersections of quasi compact opens is compatible with restriction maps"`: eight hits
  (`StructureSheaf.res_apply`, `Scheme.Hom.app_appIso_inv`, `ModuleCat.Tilde.toOpen`,
  presheaf compatibility, open-immersion formulas and Flat's local restriction lemma);
  none is the item.
- `rg` in the permitted `lean/WeilConjectures` and `lean/Sheaf` trees, first on section/base
  change/tensor patterns, then `pushoutSection` and the proposed declaration names, and
  the node-id search in WeilConjectures: no exact theorem and no name clash.
  `IntersectionSectionsFlatBaseChange` concerns sections on arbitrary intersection
  subspaces, using inverse-image sheaves; it is the downstream consumer of this finite
  open refinement, so importing it would reverse the dependency. Its `intersection*`
  helpers concern those subspace sheaves, not the ordinary open sections defined here.
  `IntersectionStructureSections.intersectionOpenDiagram` uses distinct original opens
  indexed by reverse inclusion, not the nonempty finite-subset refinement here.
  Other upstream hits concern affine charts, modules, coefficients or stalks; none
  gives the entire assertion on qc opens and compatible T-algebra comparisons.
- The proposed names were also searched in `dag/lean_names_upstream.json`: no matches.

Source checked directly: `literature/stacks-project/more-groupoids.tex`,
`lemma-affine-base-change` (Tag 0APJ), including its proof's directed refinement and
reference to flat cohomology base change. The node is an explicit finite-refinement
expansion of those sentences. No STATEMENT-DISPUTED condition or node fault was found.

Validation: the prescribed `scompile.py Q76 lem-a1-qc-open-flat-section-diagram` compiled
both the renamed sandbox module and final library module cleanly (2.9 s and 4.0 s),
without errors or warnings. Auto-implicit binding is disabled; u and v are explicit.
Earlier elaboration errors were repaired by fixing the open in the scalar-map definition,
explicitly supplying bundled algebra carriers and the Scheme category at coercion sites,
and giving `Directed` its identity family. No limits, hypotheses or statement were changed.

## Second reading by Q76

A separate sequential rereading compared the node with the completed signature and
inspected every helper body. It confirmed the nonempty finite-subset order is inclusion,
V_G maps into V_F, the inverse-image inclusion has the same direction, and the last
square has source A_F tensor T and target B_G. It checked that the algebra action on
both B_F and A_F is the structural scalar map, and that the tensor uses the right-factor
T action. The pure-tensor normalization ensures the existential isomorphisms are canonical.
The four geometric properties per F and quasi-separatedness of X are all present; arbitrary
index universe and empty opens remain allowed. The helper restriction proofs use only
functoriality and real maps; no helper theorem with an unrecorded sorry was introduced.
No mathematical mismatch was found. This is a rereading by the dispatched worker, not a
claim of an independent agent review: the brief prohibits starting other agents and
reserves the independent review to the maintainer's review of the delivery.
