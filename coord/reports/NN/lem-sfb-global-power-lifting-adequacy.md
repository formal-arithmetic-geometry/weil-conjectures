## Worker report

The module `Sheaf.AlgebraicGeometry.GlobalPowerLiftingAdequacy` states
`CategoryTheory.adequateModuliSpace_of_global_power_lifting`, with one `sorry` and
no new definitions or proofs. It gives adequacy and explicitly includes the
positive-power lifting conclusion on every affine etale base change. The node's
statement and proof are unchanged. Three already landed definition owners are
added to `stmt_deps`: `def-sfb-stack-qcqs-morphism`,
`def-sfb-relative-moduli-inertia`, and `def-trf-scheme-algebraic-space`.
There are no new nodes or dependency repairs.

The source was read online at https://arxiv.org/html/1005.2398v3:
Lemma 4.1.8(3) implies (2), Remark 4.1.3, Definition 5.1.1 and Remark 5.1.2.
The unrestricted-algebra formulation has no Noetherian hypothesis; the separate
Noetherian alternatives in the source do not enter this statement.

Hypothesis and conclusion correspondence:

- The field is `{k : Type u} [Field k]` using Mathlib's `Field`.
- The commutative k-algebra is `(A : Type u) [CommRing A] [Algebra k A]`.
  Its structural scheme map is `Spec.map (CommRingCat.ofHom (algebraMap k A))`.
- The algebraic stack over k is `F : BasedCategory.{v, w} (Over (Spec (.of k)))`
  together with `hF : IsAlgebraicModuliStack F`. No DM, representability,
  smoothness of the stack, or finite-type condition is added.
- Stack quasi-compactness is `_hFqc : IsQuasiCompactModuli F`.
  Stack quasi-separatedness is `_hFqs : IsQuasiSeparatedAlgebraicModuliMap
  (moduliBaseStructure F)`. Since the base is the spectrum of a field, hence
  separated, this is equivalent to absolute quasi-separatedness. These two
  retained hypotheses are redundant for applying the more general recorded
  affine criterion, which is why their binder names start with underscores.
- The specified k-morphism is `φ : BasedFunctor F (discreteModuli (yoneda.obj
  (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))))))`. The target is
  the actual Yoneda representable sheaf of Spec A, not an arbitrary space.
- Morphism quasi-compactness is `hqc`, with exactly the test universes of the
  adequate-moduli definition; quasi-separatedness is `hqs`.
- The induced canonical ring map is an isomorphism precisely when `hfunctions`
  holds. Every compatible family `t` has a unique scalar preimage `r : A`,
  and its value on every `x : F.obj` is the actual scheme pullback of `r`.
  `Scheme.ΓSpecIso.inv` identifies A with functions on Spec A; `yoneda.preimage`
  recovers the morphism of schemes from the chart map; `eqToHom` transports
  along the existing based-functor equality; `ULift.up` is the existing
  structure sheaf's coefficient transport. This formula is copied from the
  recorded affine criterion, and expresses bijectivity of the canonical ring
  homomorphism, rather than existence of some unrelated isomorphism.
- `hpower` binds every pair `B C : ModuliAlgebraSheaf F hF.1.1`, requires
  `IsQuasicoherentModuliAlgebra` of both, and quantifies over every morphism q
  satisfying `IsSurjectiveModuliAlgebra q`. The latter means local section
  lifting as sheaves, not surjectivity on global sections. It then binds every
  `t : moduliGlobalSectionsRing C.right` and gives `N : ℕ`, `0 < N`, and a
  compatible global section s. Equality on all objects `x : F.objᵒᵖ` is exactly
  equality of the image of s with the power of t in the global-sections ring.
- The first conclusion is `IsAdequateModuliSpace F hF (schemeSpace ...) φ`.
- The second conclusion binds every `W` in that target's `EtaleSite` and
  assumes only `IsAffine` of its underlying scheme. Its B and C are arbitrary
  algebra sheaves on `moduliSpaceBaseChange ... φ W`, with its existing fibred
  witness. There is no hypothesis that they descend from F. Quasi-coherence,
  local surjectivity, the global target section, the strictly positive exponent,
  the source section and equality on every object reproduce the same lifting
  condition on this actual 2-fibre product.
- Neither the hypotheses nor either conclusion assumes Noetherianity, finite
  generation, a characteristic restriction, nonemptiness, or a nonzero A.

Recorded dependency declarations used:

- `def-weil-field`: Mathlib `Field` (Algebra.Field.Defs).
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme`; its canonical functions identification is
  `AlgebraicGeometry.Scheme.ΓSpecIso`.
- `def-sfb-adequate-moduli-space`: `CategoryTheory.IsAdequateModuliSpace`,
  `Sheaf.AlgebraicGeometry.AdequateModuliSpace`. Its public dependencies supply
  `ModuliAlgebraSheaf`, `IsQuasicoherentModuliAlgebra`,
  `IsSurjectiveModuliAlgebra`, `moduliGlobalSectionsRing`,
  `moduliStructureSheaf`, `moduliSpaceBaseChange` and its fibred witness from
  `Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra`; these existing
  declarations and their full docstrings/signatures were inspected.
- `def-sfb-stack-qcqs-morphism`: `IsQuasiCompactModuli`,
  `IsQuasiCompactAlgebraicModuliMap`, `IsQuasiSeparatedAlgebraicModuliMap`,
  `Sheaf.AlgebraicGeometry.StackQcqsMorphism` (publicly imported by the
  adequate-moduli definition).
- `def-sfb-relative-moduli-inertia`: `CategoryTheory.moduliBaseStructure`,
  `Sheaf.AlgebraicGeometry.RelativeModuliInertia`.
- `def-trf-scheme-algebraic-space`: `AlgebraicGeometry.AlgebraicSpace.schemeSpace`,
  `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`.
- Proof dependency `lem-sfb-adequate-moduli-etale-locality`:
  `CategoryTheory.adequateModuliSpace_iff_affine_global_power`,
  `Sheaf.AlgebraicGeometry.AdequateModuliEtaleLocality`, imported without public.
  The proof docstring explains the criterion application and unfolding of the
  final conjunct of `IsAdequateModuliSpace`, matching both DAG proof steps.

Edge cases checked: N = 0 is excluded by `0 < N`; exponent one remains allowed.
The zero ring A and empty stack are permitted; on an empty test the section
rings have the unique zero section and exponent one works. Arbitrary
characteristics and non-Noetherian algebras are included. No finite-generation
or descent requirement is hidden in either algebra quantifier. Object and
morphism universes v,w are independent, and the existing coefficient universe
`max (u + 1) v w` is preserved. All variables/universes are explicitly bound;
`autoImplicit` is disabled. No file-local notation or instance is used.

Searches performed on 2026-10-24:

- `msearch.py NN lem-sfb-global-power-lifting-adequacy leanfinder` with query
  "Global power lifting for all quasi coherent algebra surjections implies
  adequate moduli space over an affine scheme": eight scheme affine-property
  results; none states this algebraic-stack implication.
- The same wrapper, `loogle`, query
  "IsAdequateModuliSpace, IsQuasiCompactAlgebraicModuliMap": no hits,
  unknown Mathlib identifier `IsAdequateModuliSpace`.
- The same wrapper, `leansearch`, query "Global section power lifting criterion
  adequate moduli space affine base": eight affine-scheme and power-basis
  results; no algebraic-stack criterion.
- The same wrapper, `grep`, query
  `adequateModuli|adequatelyAffine|power.lifting`: zero Mathlib hits.
- `rg` on both live-source directories `lean/WeilConjectures` and `lean/Sheaf`
  for `adequateModuliSpace|IsAdequateModuliSpace|global.power.lift|GlobalPower`:
  found the recorded more general affine iff criterion and the adequately-affine
  criterion, but no declaration with this item's full hypotheses and explicit
  base-change conclusion. The source files were opened in full.
- `grep -rn` for this item's id in `lean/WeilConjectures`: no hits.
- `rg` on `dag/lean_names_upstream.json` for the chosen theorem name and
  `IsAdequateModuliSpace`: no hits.

No statement dispute or source fault was found. The retired CompactObject
example module was read, as was its current node attachment and the actual
upstream CompactObject module. Both required server compilation passes succeeded
without errors or warnings (18.3 s sandbox and 15.7 s library).

## Second reading by NN

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
