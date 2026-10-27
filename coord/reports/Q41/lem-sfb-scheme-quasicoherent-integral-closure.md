## Worker report

The module `Sheaf.AlgebraicGeometry.SchemeQuasiCoherentIntegralClosure` states
`AlgebraicGeometry.Scheme.exists_quasiCoherent_stalkwiseIntegralClosure`, with its
whole proof postponed by `sorry`. The node is unchanged except for `lean`.
The source was read directly: `literature/stacks-project/morphisms.tex`,
Tag 035F, lemma-integral-closure, lines 13843–13875. Its three assertions and the
node agree. No statement correction, new node, dependency repair or mathematical
dispute is needed.

Hypothesis and clause correspondence:

- An arbitrary scheme Y is `(Y : Scheme.{u})`, with `u` explicitly declared.
- The commutative O_Y-algebra sheaf B is `(B : Y.CommAlgebraSheaf)`; this is the
  existing category `Under Y.sheaf`, so its structure morphism is `B.hom`.
- Quasi-coherence of its underlying module is
  `(hB : Y.IsQuasiCoherentAlgebra B)`, the dependency's actual predicate, defined
  to mean `B.toModule.IsQuasicoherent`.
- The specified D is rendered by `∃ (D : Y.CommAlgebraSheaf) (ι : D ⟶ B)` together
  with sectionwise injectivity and the image condition on EVERY open V. For
  every `b : B.right.obj.obj (op V)`, membership in `Set.range
  (ι.right.hom.app (op V))` is equivalent to integrality of its germ at every
  `(y : Y)` with `(hy : y ∈ V)`. Thus the existential does not choose an arbitrary
  map or an unrelated isomorphic algebra: its section images are exactly the
  prescribed subsets. Naturality of `ι` supplies precisely the inherited
  restrictions; its being a morphism in Under supplies algebra compatibility.
- The structure map on stalks is
  `((TopCat.Presheaf.stalkFunctor CommRingCat y).map B.hom.hom).hom`.
  `RingHom.IsIntegralElem` means a zero of a monic polynomial under THAT map.
  The germ is Mathlib's `TopCat.Presheaf.germ (C := CommRingCat)`.
- The conclusion that D is quasi-coherent is `Y.IsQuasiCoherentAlgebra D`.
- For EVERY point y, the stalk inclusion is the actual induced map
  `(TopCat.Presheaf.stalkFunctor CommRingCat y).map ι.right.hom`. It is injective,
  and its image consists exactly of the elements integral under the given
  structure map, as expressed by the following `∀ b` equivalence. The ring
  stalk is the same sheaf germ construction as the module stalk, retaining
  its multiplication and structural scalar action; no replacement stalk or
  arbitrary algebra instance is introduced.
- For EVERY affine open V, `IsAffineOpen V → ∀ b, ...` says that the image of
  its section inclusion is exactly `(B.hom.hom.app (op V)).hom.IsIntegralElem b`.
  This is integral closure under the specified section structure map.
- There are no reducedness, Noetherian, separation, finite-type, injective
  structure-map, or nonemptiness hypotheses.

Dependencies read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and morphisms.
- `WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebra`:
  `AlgebraicGeometry.Scheme.IsQuasiCoherentAlgebra`, based on
  `Scheme.CommAlgebraSheaf` and `Scheme.CommAlgebraSheaf.toModule` from
  `WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf`. Their full definitions
  were read; these are the existing algebra and module encodings.
- `WeilConjectures.Topology.PresheafModuleStalkFunctor`:
  `PresheafOfModules.moduleStalkFunctor`, `stalkObj`, and `stalkMap` were read.
  They bundle Mathlib's existing colimit stalks, not a separate construction.
  The statement retains the commutative-ring version of that colimit through
  `TopCat.Presheaf.stalkFunctor` and `germ`, whose signatures were also read.
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`: `integralClosure`, whose
  carrier is `IsIntegral`; its underlying `RingHom.IsIntegralElem` from
  `Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs` is used directly to
  avoid changing the supplied algebra structure map.

The proof plan imports `Mathlib.AlgebraicGeometry.Modules.Tilde`
(`tilde`, `tilde.toOpen`, `tilde.toStalk`, `tilde.adjunction`, and
`Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent`),
`Mathlib.RingTheory.Localization.Integral` (`IsLocalization.integralClosure`),
`Mathlib.Algebra.Module.LocalizedModule.Basic` (`LocalizedModule`), and
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`
(`Scheme.Modules.isQuasicoherent_of_forall_isAffineOpen`). These recorded
interfaces were read. The prime-local integrality criterion
`lem-sfb-integral-element-prime-local-criterion` has no recorded declaration
or Mathlib match yet, so there is no proof import to add for it. It is only a
proof dependency and introduces no missing object in this statement. The
four-step proof in the docstring follows all four node proof steps.

Edge cases checked mathematically before writing: Y may be empty; the stalk
clauses then have empty quantification, and empty-open sections are the zero
ring on both sides. The all-open condition over the empty open is accordingly
vacuous but its section image is the entire singleton ring. Nilpotents cause
no issue (they are integral), and noninjective structure maps and zero-ring
algebras remain allowed by `RingHom.IsIntegralElem`. Nonaffine opens only
use stalkwise integrality; the statement deliberately requires global section
integrality only on affine opens. No affine-cover, quasi-compactness or
quasi-separatedness condition has been inserted.

Searches (all on 2026-10-24):

- `msearch.py ... leanfinder "The stalkwise integral closure subsheaf of a quasi
  coherent algebra on a scheme is quasi coherent with integral closure on
  affine sections"`: eight hits on integral scheme morphisms and normalization;
  no statement for an arbitrary quasi-coherent algebra sheaf.
- `msearch.py ... loogle "RingHom.IsIntegralElem, integralClosure"`: zero hits.
- `msearch.py ... leansearch "Integral closure subsheaf of a quasi coherent sheaf
  of algebras on a scheme"`: eight hits, including `integralClosure` and
  `IsIntegralClosure`, all ring-level results.
- `msearch.py ... grep "integralClosure|integral.closure" AlgebraicGeometry`:
  five hits in Mathlib normalization. Read `Scheme.Hom.normalizationDiagram`:
  it concerns pushforward sections of a scheme morphism and is not this
  all-open stalkwise subsheaf theorem for an arbitrary algebra.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf`, by integral-closure
  terms and the item id, and a narrower search for `stalkwiseIntegralClosure`,
  stalkwise/integral combinations: no matching existing scheme theorem.
  Read `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentIntegralClosure`:
  its small-etale algebraic-space statement is a distinct consumer of this
  scheme result and does not supply the Zariski all-open or stalk conclusions.

## Second reading by Q41

Self-check performed with the node, source and final Lean file open; no other
agent was started, as the dispatcher brief explicitly prohibits it. The
maintainer's independent reading remains the independent review.

Checked each binder: arbitrary Y, existing B, and exactly its module
quasi-coherence hypothesis. Checked each conclusion against Tag 035F:
sectionwise injectivity plus the all-open image formula identifies precisely
the defined subsheaf, the Under morphism preserves algebra and restrictions,
D has the required quasi-coherent underlying module, the induced stalk map
is injective with the integral elements as its exact image, and the affine
section formula uses the original structure homomorphism. No source hypothesis
or clause is missing. No mathematical mismatch was found. During compilation,
field-style `germ`/`stalk` notation was replaced with explicit Mathlib functor
applications to resolve elaboration; this did not change any mathematical object.
All variables and the universe are explicitly bound, and no local notation,
local instance, helper definition or data chosen from an existence sorry is used.
