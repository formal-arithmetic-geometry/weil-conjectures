## Worker report

Defines `AlgebraicGeometry.RelativeTangentBundle.scheme` in
`Sheaf.AlgebraicGeometry.RelativeTangentBundle`, with the structural projection,
augmentation, zero section, and affine comparisons specified by pur9-dg-def-tangent.
The node statement is unchanged. No new nodes or dependency repairs are needed.

Hypotheses and clauses, checked against the final node and module:

- Schemes and morphism: explicitly declared universe `u`, section parameters
  `{X Y : Scheme.{u}} (f : X ⟶ Y)`. Smoothness is `[Smooth f]`. No Noetherian,
  quasi-compactness, separatedness, nonemptiness, or fixed-rank assumption is added.
- `F = Ω_{X/Y}` is the recorded `f.relativeDifferentials`; its affine-local
  description is the existing differential-sheaf construction, not a new module sheaf.
- Quasi-coherence of F is the published instance
  `AlgebraicGeometry.relativeDifferentials_isQuasicoherent f`. It needs locally finite
  presentation, which follows from `[Smooth f]`; no new hypothesis is supplied.
- `A = Sym(F)` and its generator map are exactly
  `SymmetricAlgebraSheaf.algebra f.relativeDifferentials` and
  `SymmetricAlgebraSheaf.inclusion f.relativeDifferentials`. `algebraObject` packages
  this algebra with the first clause of `quasiCoherentSymmetricAlgebra_affine_comparison`.
  Its second clause supplies the affine section identification used by `affineChart_spec`.
- The relative spectrum is `over`, the unop of the inverse of the existing concrete
  structure-algebra anti-equivalence, applied to `algebraObject`. `scheme` is its
  underlying scheme, and `projection` is its actual structural map. `algebraIso`
  is the inverse counit identification of Sym(F) with the direct-image structure algebra.
  This uses a quasi-inverse of a fully specified equivalence, not an arbitrary scheme
  selected from an uncharacterized existence assertion.
- The augmentation is `VectorBundleZeroSection.augmentation X f.relativeDifferentials`.
  Its existing definition chooses the *unique* map furnished by
  `exists_quasiCoherentSymmetricAlgebra_core X F (Under.mk (𝟙 X.sheaf)) 0`.
  The existing `VectorBundleZeroSection.augmentation_spec` states that it kills
  `inclusion`, is the unique such algebra map, and on sectionwise symmetric algebras
  is `SymmetricAlgebra.algebraMapInv`. It fixes constants because it is an under-category
  morphism. No alternative augmentation notion is defined here.
- The identification of relative Spec(O_X) with X is implemented using
  `VectorBundleZeroSection.baseObject X`, the identity X-scheme. Its image under the
  concrete structure-algebra functor is its direct-image structure algebra. The
  published `augmentationToBase` is the unique zero-generator extension into this
  algebra, hence transports the same augmentation through the canonical scalar
  identification. `zeroSectionOver` is its fully faithful inverse image, with the
  counit identifying the source algebra of that map. The contravariant direction is
  baseObject X → over f, so `zeroSection` has type X → T_{X/Y}.
- `zeroSection_comp_projection` states `zeroSection f ≫ projection f = 𝟙 X`.
  Its proof is postponed, with its complete over-category proof in the docstring.
  `zeroSectionRestricted` uses that named theorem to form the restriction to U.
- For every `U : X.affineOpens`, `affineChart` goes from π⁻¹(U) to
  `Spec (SymmetricAlgebraSheaf.sections f.relativeDifferentials (op U.1))` using
  the sheafification unit and `algebraIso`. `affineChart_spec` asserts it is an
  isomorphism, matches the projection with Spec of the scalar inclusion, and gives
  `zeroSectionRestricted f U.1 ≫ affineChart f U = U.2.isoSpec.hom ≫ Spec.map ...`,
  where the ring map is `SymmetricAlgebra.algebraMapInv`. This is precisely the
  affine zero section fixing constants and killing degree-one generators.

Dependency interfaces read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, `Spec.map` (available through the public construction imports).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`
  (publicly imported by the recorded differentials module).
- `WeilConjectures.AlgebraicGeometry.Modules.Differentials`:
  `AlgebraicGeometry.Scheme.Hom.relativeDifferentials`, with its affine and restriction
  comparisons read in the source.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: imports the recorded coherence module;
  the quasi-coherence clause used here is Mathlib's `SheafOfModules.IsQuasicoherent`,
  the same predicate used by the symmetric-algebra and relative-Spec dependencies.
- `Sheaf.AlgebraicGeometry.SymmetricAlgebraSheafConstruction`:
  `SymmetricAlgebraSheaf.algebra`, `inclusion`, `sectionMap`, `sections`.
- `Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebraCore`:
  `exists_quasiCoherentSymmetricAlgebra_core`, through the existing augmentation helpers.
- `Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebraAffine`:
  `quasiCoherentSymmetricAlgebra_affine_comparison`.
- `WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec`:
  `affine_morphism_relative_spec`, through the concrete equivalence provided by the
  published vector-bundle module.
- `Sheaf.AlgebraicGeometry.VectorBundleZeroSection`:
  `structureAlgebraFunctor`, `antiEquivalence`, `baseObject`, `augmentation`,
  `augmentationToBase`, `augmentation_spec`. All these helpers are general in the base
  scheme and module. The Noetherian/constant-rank wrappers `scheme`, `over`, and `zero`
  from that module are deliberately not used as the tangent construction.
- `Sheaf.AlgebraicGeometry.DthFittingSmoothLocus`:
  `relativeDifferentials_isQuasicoherent`. The owning node also records this helper in
  `lean.declarations`. Both helper-owner nodes are added to the item's `stmt_deps` under
  the standing permission to cite landed nodes; neither node is modified. A graph traversal
  found no dependency path from either helper owner back to this item.

Sources checked: the current blueprint's entire pur9-dg-def-tangent definition and
Stacks `constructions.tex`, definition-vector-bundle (01M2), together with the complete
recorded relative-spectrum theorem and the augmentation construction. These use the
EGA convention Spec Sym(F), so no dual is inserted into the symmetric algebra.

Edge cases: for the identity or an etale morphism Ω vanishes, so Sym(Ω) is O_X and the
relative spectrum/zero section are X and its identity up to the canonical isomorphism.
For affine space over an affine base the construction is the usual polynomial algebra
in the differential generators, and the zero section sends all those generators to zero.
Disconnected schemes with differing smooth relative dimensions remain admitted: there
is no single global rank parameter. Empty X gives the empty relative spectrum, with its
unique section from X; no point or nonempty affine chart is chosen. Trivial section rings
also remain permitted. The one scheme universe is the existing Scheme-category convention.

Searches (all before writing the construction):

- `msearch.py ... leanfinder` with “Relative tangent bundle of a smooth scheme morphism
  is relative Spec of the symmetric algebra of relative differentials with augmentation
  zero section”: eight hits, including specTargetImage, formally-unramified Spec lmul,
  and Kaehler differential/cotangent constructions; none is this tangent-bundle scheme.
- `msearch.py ... loogle "SymmetricAlgebra, AlgebraicGeometry.Scheme"`: OK, zero hits.
- `msearch.py ... grep "tangentBundle|relativeTangent|relative_tangent|relativeSpec|RelativeSpec"
  AlgebraicGeometry`: OK, zero Mathlib hits.
- `msearch.py ... leansearch` with “The relative tangent bundle of a smooth scheme
  morphism is Spec of the symmetric algebra of relative differentials, with zero section
  induced by augmentation”: eight hits, mainly manifold bundles and ring differentials;
  no matching scheme construction.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for tangentBundle, relativeTangent,
  relative_tangent, RelativeTangent and the item id: no matching declaration.
- `rg` for relativeSpec/relativeSpectrum/RelativeSpec and quasi-coherence of differentials
  found the recorded relative-spectrum theorem, the general vector-bundle helpers and
  the existing differential quasi-coherence theorem used here. The constant-rank vector
  bundle itself is not an exact existing match for this node. The upstream-name index
  has no relative-tangent declaration either.

Definitions contain real data. The two postponed theorems are
`RelativeTangentBundle.zeroSection_comp_projection` and
`RelativeTangentBundle.affineChart_spec`; both state clauses already present in this
node and carry source and complete natural-language proof docstrings. No independent
mathematical statement has been introduced without a node. No statement dispute or
source correction is required.

Validation: `scompile.py` compiles both the sandbox module and its final library module
successfully (5.0 s and 5.9 s), with no errors or unexpected warnings. The first pass's
restriction elaboration fault was repaired by using the named section identity.

## Second reading by Q98

The dispatched worker reread the final node and module together; the brief forbids
starting another agent, and the maintainer supplies the independent review. This pass
checked each hypothesis and clause against the correspondence above. In particular,
`Smooth f` is the only geometric assumption; the existing quasi-coherence helper needs
no added flatness or fibre-dimension input. The symmetry convention is Sym(Ω), not
Sym(Ω dual). The full-subcategory opposite reverses the augmentation in the right
way, and the affine chart equation uses Spec of a ring map Sym(F(U)) → O_X(U), with
source U. The scalar and zero-generator requirements are supplied by the existing
augmentation specification. No mismatch was found and no node statement changed.
The only implementation repair was replacing an unsuccessful rewrite through opaque
projection wrappers with the explicitly named section theorem before defining the
restriction. No independent-reader identity is claimed for this worker's second pass.
