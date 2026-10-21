## Worker report

The module `Sheaf.Paper.CommonLinePositiveScalarPowers` states
`SheafOfModules.CommonLine.exists_positiveScalarPowers` and the coefficient-naturality
clause `SheafOfModules.CommonLine.exists_coefficientNaturality`, both with `sorry`.
The helper structures spell out the normalized data asserted by this one node.
The module introduces no additional independent mathematical notion and takes no
ring/module comparison as an extra hypothesis. The main theorem supplies them.

The node is unchanged except for `lean` and adding the already recorded
`def-sp-scalar-tensor-comparison-data` to `stmt_deps`, because the module uses its
`scalarTensorPower` (including degree zero) and `scalarExtensionSection` verbatim.
No statement correction, new node, or dependency repair is needed.

Hypothesis and clause correspondence:

- A site with finite limits and final object is `{C : Type uC} [Category.{vC} C]`,
  `{J : GrothendieckTopology C}`, and `[HasFiniteLimits C]`. Finite limits include
  the terminal object. `[EssentiallySmall.{u} C]` expresses smallness relative to
  the common sheaf universe. The usual `HasSheafCompose`, `WEqualsLocallyBijective`,
  and `HasWeakSheafify` instances expose the sheafification available under that
  size convention. Site object and morphism universes remain independent.
- The sheaves B,A,C_0,C_1 are `B A D₀ D₁ : Sheaf J CommRingCat.{u}`.
  The maps are `a`, `c₀`, `c₁`, `φ`, with `hφ : c₀ ≫ φ = c₁`, precisely saying
  that φ is a B-algebra map. T ranges over every `Modules A` in the conclusion;
  local freeness is not assumed for the presentations or comparisons.
- `Modules` is a transparent application of the recorded `ringedSiteModules`;
  `restrict` is Mathlib `SheafOfModules.restrictScalars`, `regular c` is the
  regular module of the algebra sheaf restricted to B, and `tensor` is exactly
  the recorded `siteSheafTensorRight` object. These abbreviations introduce no
  copied categories, tensor products, scalar actions, or chosen structures.
- `Coefficients a c` supplies R_i, its A and C_i structure maps, their B-balance,
  and a B-linear isomorphism `tensorIso` from the actual sheaf tensor
  `regular a tensor_B regular c` to the underlying B-module of R_i.
  `tensor_tmul` identifies a tensor c with left(a) right(c).
  Because left and right are ring sheaf maps, the product of two such elements
  is left(aa') right(cc'), and their unit is left(1) right(1)=1. This expresses
  exactly the specified tensor-ring multiplication and unit, with the underlying
  sheaf tensor fixed by an isomorphism. R_i is supplied by the theorem, rather
  than posited as unrelated input or chosen by a definition from mere existence.
- `Presentation K` supplies L_i for each T and `underlying T`, identifying its
  underlying B-module with the actual sheafified tensor of T restricted to B
  and C_i. It also supplies the R_i-linear `common T` from the existing
  `changeOfRingsOfUniverses K.left T` to L_i. Thus L_i has the tensor-product
  meaning in the node, with the required R_i-action.
- `common_tmul` says i_i(t tensor (a tensor c))=at tensor c, with the ring tensor
  represented by left(a) right(c). `inverse_tmul` is precisely the stated
  inverse t tensor c mapped to t tensor (1 tensor c).
  Scalar-extension notation in the library puts the scalar first.
  R_i-linearity follows from the categorical type of `common` and its inverse.
- `Presentation.naturality` says that i_i is natural in T, comparing the actual
  B-tensor functor's map with the conjugate of the existing A-scalar-extension
  map. `Presentation.map` merely names this explicit conjugate.
- `iota_left` and `iota_right` identify iota as id_A tensor φ.
  `transition_tmul` identifies the coefficient-change map of L_i as id_T tensor φ.
  `common_square` is the common-presentation square, including arbitrary R_0
  scalar r, and sends its coefficient to iota(r).
- The P_i(n) are exactly the recorded `scalarTensorPower` of `presentation_i.line T`:
  P_i(0) is the regular module of R_i, P_i(1)=L_i, and subsequent powers are
  left associated. `comparison T n` is the R_1-linear isomorphism b_n for every n.
- `zero_tmul` is b_0(r tensor s)=iota(r)s.
  `one_tmul` is the displayed b_1 formula through i_0 and i_1.
  `one_inverse` is its displayed inverse, with scalar factor 1 on the R_0 side.
- `succ_tmul` gives b_(n+2) on ((x tensor y) tensor s) as
  b_(n+1)(x tensor s) tensor b_1(y tensor 1). This characterizes the canonical
  relative binary tensor comparison followed by b_(n+1) tensor b_1. It is a
  formula on local nested pure tensors, so it specifies the whole sheaf map
  by the recorded tensor/sheafification universal properties.
- `PositiveScalarPowers.naturality` is the naturality square of b_n in arbitrary
  A-linear maps T to T', using `scalarTensorPowerMap` on both sides.
- `same_cover` quantifies over an arbitrary index universe uI, a family U:I→C,
  and `J.CoversTop U`. If each `T.over (U i)` is isomorphic to its regular A-module,
  it supplies a regular-module isomorphism for each P_0(n) and P_1(n) on that
  very U i. It neither refines nor replaces the cover.
- `sectionPower` recursively forms e_i^n using the existing pure-tensor section
  constructor, with the actual ring unit in degree zero.
  `generator_tmul` quantifies over every local frame on every slice C/U and every
  V→U. Its section e is `frame.hom.val.app (op V) 1`; e_i is i_i(e tensor 1).
  Its equation is exactly b_n((r e_0^n) tensor s)=iota(r)s e_1^n, including n=0.
- `exists_coefficientNaturality` supplies naturality for every commuting diagram
  of B-algebra coefficient maps β₀,β₁. `PresentationChange` specifies the induced
  ring map and maps on powers by their degree-zero, degree-one and recursive
  pure-tensor formulas. `CoefficientNaturality.extension_tmul` specifies the map
  on scalar extensions, and `square` is its commutative square with the two b_n.
  No arbitrary maps are substituted for these canonical coefficient maps.
- All maps are actual module sheaf morphisms after the indicated scalar
  restriction. All formulas quantify over local sections in Cᵒᵖ or slice objects.
  Hence all maps, formulas and their defining pure tensors commute with restriction;
  no assertion that every sheaf section is globally a pure tensor is made.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`; its retained Grothendieck-topology
  and sheaf interfaces apply to the finite-limit site here.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, with its public tensor interfaces
  `siteSheafTensorRight`, `siteSheafTensorTmul`, `changeOfRingsOfUniverses`, and
  `changeOfRingsHomOfUniverses`. These use the actual presheaf tensor followed
  by module sheafification, without equating the two site universes.
- `Sheaf.Paper.InvertibleTensorScalarExtensionDefinitions`:
  `SheafOfModules.scalarTensorPower`, `scalarTensorPowerMap`, and
  `scalarExtensionSection`, via the added recorded definition dependency.
- Mathlib `SheafOfModules.unit`, `restrictScalars`, and `over`;
  `GrothendieckTopology.CoversTop`, `Sheaf`, and `GrothendieckTopology`.
- Proof imports: upstream `SheafOfModules.tensor_bilinear_universal`;
  Mathlib `PresheafOfModules.sheafification` and `sheafificationAdjunction`;
  `PresheafOfModules.exists_bilinear_sheafification_extension` and
  `unique_bilinear_sheafification_extension` in the two recorded Sheaf modules;
  `SheafOfModules.exists_scalarExtensionTensorCore` in
  `Sheaf.Paper.ScalarExtensionBinaryCoherence`; and
  `SheafOfModules.exists_localizedSiteTensorRestriction` in the recorded
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction`.

Sources read: the current blueprint proof `prop-weil-twist-preserves.proof.md`,
first scalar-extension/tensor-power sentence and final integral-coefficient sentence;
`sites-modules.tex`, section-tensor-product (03EK), the sheafification/tensor and
Hom/Bilin paragraphs, and lemma-tensor-product-pullback (03EL).
The theorem docstrings give the node's seven-step natural-language proof, including
bilinear extension across nested sheafifications.

Edge cases checked before writing: n=0 (regular modules, multiplication), n=1
(the common-presentation transitivity and inverse), n=2 (binary comparison), T=0,
non-free T, zero coefficient rings, identity coefficient maps, and non-flat maps
such as Z→Z/2. None needs a flatness hypothesis. Empty covering families in a
trivial sheaf situation are admitted; same_cover is a universal claim on their
members and imposes no nonemptiness. Rank-one over the zero ring is represented
by an isomorphism to its regular module. Frame changes multiply both sides of the
normalized generator formula by the corresponding nth power.

Searches made with the prescribed msearch.py wrapper:

- leanfinder: "Sheaf of tensor product of commutative algebras and common module
  presentation tensor powers base change". Eight hits, mostly algebraic
  `Algebra.Presentation`/`PreSubmersivePresentation` base-change constructions;
  none states the sheaf common-line lemma.
- loogle: "TensorProduct.AlgebraTensorModule.assoc,
  TensorProduct.AlgebraTensorModule.distribBaseChange". Zero hits for the joint query.
- grep: "tensorProduct|TensorProduct|pushout" in Algebra/Category/ModuleCat/Sheaf.
  Zero hits; scalar restriction alone does not construct this package.
- leansearch: "Sheafified tensor product of algebra sheaves common module
  presentation nonnegative powers base change". Eight hits, including the algebraic
  `TensorProduct.AlgebraTensorModule.distribBaseChange` and the Cartesian
  `CategoryTheory.Sheaf.tensorProd_isSheaf`; neither gives module sheaf tensors
  with the common presentations, powers, original covering and normalization.
- rg in `lean/WeilConjectures` and `lean/Sheaf`: commonLine/common.line,
  tensorRing/ringTensor/CommonLine, tensor and scalar-extension file names, and
  the exact node id. No exact existing theorem. Read the existing scalar-tensor
  comparison data and binary coherence, tensor functoriality, tensor universes,
  and slice restriction interfaces. The recorded scalarTensorPower is reused;
  the neighboring invertible scalar-extension theorem assumes a line and lacks
  the two common coefficient presentations for arbitrary T.

## Second reading by Q57

I reread the node and complete final module clause by clause in a separate audit
pass. The independent delivery review is performed by the maintainer as specified
in the dispatch brief. I checked the B-algebra commuting equation, the direction
of both underlying tensor isomorphisms, the R_i-linearity of i_i, its inverse,
the coefficient square, the n=0 and n=1 maps, the left-associated successor,
module and coefficient naturality, the original covering, and frame restrictions.
The initial compile exposed three unit sections that needed explicit ring types;
these now use typed terms, preserving their value and avoiding hidden statement lets.
I added explicit naturality squares in both variables rather than leaving the word
"natural" only in a docstring. No mathematical statement fault was found.

Validation: all compiles use scompile.py under the default 60-second limit.
The final module is checked both in its sandbox context and at its library module name.
The stage-2 dry run and delivery are performed by deliver2.py.
