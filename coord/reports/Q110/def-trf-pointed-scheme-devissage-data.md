## Worker report

Item: def-trf-pointed-scheme-devissage-data. Group: Q110. Date: 2026-10-24 UTC.
Module: `Sheaf.AlgebraicGeometry.PointedAffineDevissage`.

This module defines the auxiliary pointed scheme terminology, including elementary
étale pointed maps, one-step data, complete finite chains, and standard shrinkings
of one step or a complete chain. All definitions contain actual data. There are
no theorem declarations, postponed proofs, sorries, new nodes, dependency repairs,
or statement changes. Only the item's `lean` field changes.

The source read was `literature/stacks-project/flat.tex`: definitions
one-step-devissage (05H4), one-step-devissage-at-x (05H5), complete-devissage
(05HH), complete-devissage-at-x (05HI), shrink (05H9), shrink-complete (05HL),
and complete-devissage-algebra (05HX). The intervening shrinking proofs and
proposition-existence-complete-at-x were also read. The auxiliary omissions of
support-dimension equalities and the zero-length convention are explicit in the
DAG statement; they are retained. The latest blueprint unit sk-i-curve-zero and
its lem-trf-local-term-locality statement were read to check the recorded ancestry.
This is an auxiliary definition, not a replacement for either blueprint statement.

Clause-by-clause correspondence:

- The schemes are `Scheme.{u}` for an arbitrary explicit universe `u`, and maps
  are scheme morphisms. Initial data are the indices `f : X ⟶ B`, `F : X.Modules`
  and `x : X`; the marked base point is `f x`, so no independent base point is
  left unconstrained. `PointedAffineOneStep.locallyOfFiniteType` gives the locally
  finite type hypothesis, and `finiteType` gives precisely quasi-coherent and
  finite type. The nil constructor carries the same ambient hypotheses.
- `IsElementaryEtalePointed h u v` is `Etale h`, `h u = v`, and
  `IsIso (h.residueFieldMap u)`. This is the actual induced residue map, with
  source residue field at `h u`; the point equation identifies it with κ(v).
- A one-step datum is `PointedAffineOneStep f F x`. Its fields `Z`, `Y`, `i`,
  `π`, `g`, and `over : i ≫ f = π ≫ g` are the two B-maps in the node. The
  structural map Z → B is their common composite. The four affine hypotheses
  are `affineX`, `affineB`, `affineZ`, `affineY`.
- `closed` is `IsClosedImmersion i`. `finitePresentation` is
  `LocallyOfFinitePresentation i`. Because X and Z are affine and i is a closed
  immersion, quasi-compactness and quasi-separatedness are automatic; hence this
  is exactly finite presentation, not a weaker hypothesis here.
- `finite` is `IsFinite π`; `smooth` is `Smooth g`;
  `geometricallyIrreducible` is `GeometricallyIrreducible g`, whose defining
  field-base-change condition is precisely geometrically irreducible fibres.
  `d : ℕ` includes d = 0, and `fibreDimension` says for every b in B that the
  scheme-theoretic fibre `g.fiber b` has Krull dimension d. There is no support
  dimension hypothesis, and no requirement that d decrease along a chain.
- `G : Z.Modules`, `finiteTypeG`, and
  `presentation : (Scheme.Modules.pushforward i).obj G ≅ F` give the finite-type
  quasi-coherent module and the required pushforward identification.
  Mathlib's pushforward evaluates to G on inverse images of opens with the scalar
  action given by the scheme's structure-sheaf map, exactly as stipulated.
- `z`, `y`, `markedX`, `markedY`, and `markedBase` give the marked points and
  all three point-image equations. `singletonFibre` says every t in Z satisfies
  π(t) = y iff t = z; it includes membership as well as uniqueness.
- `purelyTranscendental` uses the recorded
  `Algebra.IsPurelyTranscendentalExtension` with the algebra structure from the
  actual `(g.residueFieldMap y).hom`. Its source κ(g(y)) is κ(f(x)) by
  `markedBase`. The extension can have an empty transcendence basis.
- `PointedAffineDevissage B f F x n` is a dependent finite list of length n.
  A cons cell carries one one-step datum s, its rank r, its map α, the generic
  fibre condition, and the next chain. The recursive input is exactly
  `cokernel α` on s.Y, with structural map s.g and marked point s.y. This renders
  both the first-datum and every successive-datum clauses without unrelated
  input modules or arbitrary identifications.
- `SheafOfModules.free (R := s.Y.ringCatSheaf) (ULift.{u} (Fin r))` is the
  existing Mathlib coproduct of r copies of the structure sheaf. ULift merely
  places the finite index type in the coefficient universe. No r > 0 hypothesis
  is imposed, so r = 0 is the zero sheaf.
- The α codomain is exactly `(Scheme.Modules.pushforward s.π).obj s.G`.
  The category X.Modules is abelian. Its `cokernel α` is the sheaf cokernel,
  hence the quotient by the image sheaf, equivalently the sheafified presheaf
  quotient in the node, rather than a pointwise presheaf quotient.
- The generic condition quantifies over every `ξ : s.g.fiber (f x)` satisfying
  `IsGenericPoint ξ Set.univ`. This fibre is the actual pullback along
  `B.fromSpecResidueField (f x)`. Its image in s.Y is `s.g.fiberι (f x) ξ`.
  Geometric irreducibility supplies an irreducible nonempty fibre; a scheme is
  sober and T0, so the generic point exists uniquely. Universal quantification
  therefore imposes the condition at exactly that point and is not vacuous.
- `IsResidueFibreIso α ξ` takes the actual stalk map using
  `RingedSpace.moduleStalkFunctor` and tensors it on the right with κ(ξ) via
  `LinearMap.rTensor`. The local ring acts through `Y.residue ξ`; this is the
  precise map H_ξ ⊗ κ(ξ) → K_ξ ⊗ κ(ξ), and its `Function.Bijective` is the
  required vector-space isomorphism. For the free source its tensor is
  canonically κ(ξ)^r. No unrelated residue-space map is supplied as a parameter.
- The nil constructor requires `IsZero F` and X,B affine. Thus n = 0 is
  permitted exactly under the node's zero-module and affine conditions (in the
  stipulated locally finite type, finite-type quasi-coherent setting). At the
  end of a positive chain this gives precisely `IsZero (cokernel α_n)`.
- `HasPrincipalRange a` says the image of a is `T.basicOpen t` for a global
  section t on the target affine T. All its uses also require a to be an open
  immersion. These are precisely the principal affine opens D(t).
- `OneStepShrinking` relates original and restricted one-step data over principal
  open immersions `aB`, `aX`, `aZ`, `aY`. `baseSquare`, `closedSquare`,
  `finiteSquare`, `smoothSquare` restrict all structure maps. `markedX`,
  `markedZ`, `markedY` retain all marked points. The base point is retained
  because baseSquare and markedX imply aB(f'(x')) = f(x).
- `moduleIso` identifies G' with the actual restriction of G; the supplied eF
  identifies F' with the actual restriction of F. `presentationSquare` requires
  the original pushforward presentation to restrict to the new one. The
  comparison `restrictionPushforwardMap` is constructed explicitly as the mate
  of the restriction unit, using Mathlib's restriction adjunctions and
  pushforward composition isomorphisms. It is never an arbitrary chosen map.
  `dimension` retains the integer belonging to the datum. Both s and s' satisfy
  every displayed one-step condition by their types.
- `StandardShrinking` performs the same restriction recursively through the
  finite chain with one fixed base immersion. Its nil case retains principal
  base and initial opens, the initial marked point and the module identification.
  Its cons case takes `OneStepShrinking` plus `alphaSquare`: the original α is
  restricted using Mathlib's `mapFree` and `restrictUnitIso`, then the actual
  pushforward restriction comparison and the G identification. The same r is
  retained. `quotientSquare` identifies the next input by the induced cokernel
  map, so the subsequent presentation isomorphism is also the restricted one.
  `tailShrinking` continues on the same principal base open. Both chain indices
  are already valid chains; every generic, finite, smooth, marked, and final
  zero condition therefore remains imposed on the restricted data.

Dependency declarations used (modules read with their declaration signatures and
source docstrings; imports include their public dependency closures):

- def-pc-scheme: Mathlib.AlgebraicGeometry.Scheme,
  `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- def-weil-finite-type-morphism: Mathlib.AlgebraicGeometry.Morphisms.FiniteType,
  `AlgebraicGeometry.LocallyOfFiniteType`.
- pqf-def-coherent: Sheaf.AlgebraicGeometry.CoherentFiniteType,
  `AlgebraicGeometry.Scheme.Modules.IsQuasiCoherentFiniteType`.
- def-weil-etale-morphism: Mathlib.AlgebraicGeometry.Morphisms.Etale,
  `AlgebraicGeometry.Etale`.
- def-weil-residue-field: Mathlib.AlgebraicGeometry.ResidueField,
  `Scheme.residueField`, `Scheme.Hom.residueFieldMap`, `Scheme.residue`.
- def-weil-affine-spectrum: Mathlib.AlgebraicGeometry.Scheme,
  `AlgebraicGeometry.Spec`; affineness uses Mathlib.AlgebraicGeometry.AffineScheme,
  `AlgebraicGeometry.IsAffine`.
- def-weil-closed-immersion: Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion,
  `AlgebraicGeometry.IsClosedImmersion`.
- def-sbc-locally-finite-presentation:
  Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation,
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- def-weil-finite-integral-morphism: Mathlib.AlgebraicGeometry.Morphisms.Finite,
  `AlgebraicGeometry.IsFinite`.
- def-sbc-smooth-morphisms: Mathlib.AlgebraicGeometry.Morphisms.Smooth,
  `AlgebraicGeometry.Smooth`.
- def-pc-geometrically-irreducible: Mathlib.AlgebraicGeometry.Geometrically.Integral
  (publicly imports Irreducible), `AlgebraicGeometry.GeometricallyIrreducible`.
- def-kun-dimension: WeilConjectures.Mathlib.Topology.KrullDimension,
  `topologicalKrullDim` from its public Mathlib.Topology.KrullDimension import.
- def-trf-purely-transcendental-extension:
  Sheaf.FieldTheory.PurelyTranscendentalExtension,
  `Algebra.IsPurelyTranscendentalExtension`.
- def-weil-pbc-module-stalk:
  WeilConjectures.Topology.PresheafModuleStalkFunctor,
  `PresheafOfModules.moduleStalkFunctor`; for sheaves over schemes the shared
  `RingedSpace.moduleStalkFunctor` from
  WeilConjectures.Algebra.Homology.ModuleStalkFunctor is used, as the dependency
  note and STATE's MODULE STALKS convention prescribe. Its stalk carrier is the
  same module stalk; no new stalk definition is made.
- def-weil-pbc-module-tensor-product: Mathlib.LinearAlgebra.TensorProduct.Map,
  `LinearMap.rTensor` and its public `TensorProduct` construction.
- def-pc-module-pullback: Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction,
  the shared tensor pullback and normalized adjunction. For open immersions the
  actual restriction functor `Scheme.Modules.restrictFunctor` is used; its
  section formula, restriction unit isomorphism and adjunction are those from
  Mathlib.AlgebraicGeometry.Modules.Sheaf. This is the usual open pullback,
  with the better definitional section formula, not a replacement notion.
- def-pc-fibre-product: Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback,
  `CategoryTheory.Limits.pullback`, used by Mathlib.AlgebraicGeometry.Fiber's
  `Scheme.Hom.fiber` and `fiberι`.
- def-sc-generic-point: Mathlib.Topology.Sober, `IsGenericPoint`.

Edge cases examined before and after writing:

- An identity one-step datum on Spec k, G = O, d = 0, singleton marked fibre,
  and the trivial purely transcendental extension satisfies the definition.
- Length zero accepts an affine zero module and rejects a nonzero module.
  A positive chain ends by requiring the final cokernel zero.
- Rank zero is allowed. Its generic condition forces the target residue vector
  space to vanish, exactly as the source; it does not assert the sheaf itself zero.
- The empty transcendence basis is allowed. Arbitrary field characteristics and
  arbitrary scheme universe u are retained.
- Empty initial schemes have no marked point, as in the node. A marked fibre is
  nonempty; geometric irreducibility prevents a vacuous generic-point condition.
- The principal open D(1) allows identity shrinkings. D(0) cannot retain a marked
  point. The nil shrinking case still remembers the principal base and initial
  opens. All ranks, dimensions and marked points are retained for cons cells.
- No equality between relative dimension and support dimension was inserted.

Searches for an existing definition:

- msearch.py leanfinder, query: `pointed affine scheme devissage finite chain
  smooth geometrically irreducible fibres singleton finite fibre cokernel generic
  point`. Eight hits: residue-field preimmersions, integral/reduced schemes,
  affine-space non-integrality, smooth chart existence, and Jacobson fibres.
  None defines the requested data or shrinking relation.
- msearch.py loogle, query: `"devissage"`: zero hits.
- msearch.py grep, query: `Devissage|devissage|dévissage`: zero Mathlib hits.
- msearch.py leansearch, query: `pointed affine scheme devissage chain with
  generic residue field basis`: eight hits on affine schemes, affine covers,
  local affineness and affine basis lemmas; no dévissage data.
- rg in lean/WeilConjectures and lean/Sheaf for
  `Devissage|devissage|dévissage`: constructible/derived-category dévissage and
  proof references, not these pointed finite-module diagrams.
- grep -rn for this exact node id in lean/WeilConjectures: no match.
- rg for `Pointed.*Devissage|pointed.*devissage|OneStepDevissage` in the two
  library roots: no existing declaration.
- rg for `IsPrincipalOpen|PrincipalOpenImmersion|principal.*open.*immersion|
  range.*basicOpen` found standard basic-open facts and localization proofs,
  not an existing predicate for the principal-range field needed here.
  The actual principal opens are the existing `Scheme.basicOpen`.

Validation: scompile.py compiled both the sandbox module and its actual library
module cleanly, including the complete shrinking definition. No warnings were
reported. The final delivery dry run compiles the delivered file again.

## Second reading by Q110

The dispatcher explicitly forbids starting other agents. This section records a
second author pass with the node and complete module open, not an independent
worker review; the maintainer provides the independent review of this delivery.

I compared all one-step fields against the first paragraph: the ambient finite
hypotheses, all four affine schemes, B-linearity, closed finite presentation,
finite π, smooth geometrically irreducible fibres with constant dimension,
finite-type G, presentation, each marked-point equality, singleton fibre, and
pure transcendence are present. The residue field at g(y) is identified with
κ(b) by markedBase, rather than assigned an arbitrary algebra structure.

I compared the constructors against the second paragraph: the first datum has
input F, successive ones have precisely the preceding cokernel, the rank may be
zero, the basis map is tested at the generic point of the scheme-theoretic fibre,
and the terminal nil forces the last cokernel zero. The separate nil case
also enforces the explicitly permitted zero-length convention and affineness.

I checked the shrinking definitions against the final sentences. Principal open
immersions retain all points and all maps. The G and F identifications preserve
the presentation square. The chain shrinking additionally preserves α with the
canonical free-source map and preserves the quotient identification used by the
next step. In particular, supplying merely another valid chain would not pass
these squares. I checked the domains and codomains of each comparison in the
Lean source and by the clean server compile. No mathematical mismatch was found;
only source-location/docstring wording was clarified after the compile. No
statement or dependency field required correction.
