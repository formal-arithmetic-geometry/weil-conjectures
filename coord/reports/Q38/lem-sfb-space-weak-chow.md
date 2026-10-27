## Worker report

The module Sheaf.AlgebraicGeometry.AlgebraicSpaceWeakChow states
AlgebraicGeometry.AlgebraicSpace.exists_proper_surjective_quasiProjective_scheme_cover.
Its only proof is `sorry`. No definitions, helper axioms, dependency repairs, or statement
corrections are introduced. The full eight-step DAG proof is included in its docstring.

Source checked: spaces-cohomology.tex, lemma-weak-chow (Tag 089J), in full;
morphisms.tex, definition-quasi-projective (Tag 01VW), especially (2);
spaces-morphisms.tex, lemma-base-change-surjective (Tag 03MH). The latest blueprint proof
sk-thm-sf-ctf-stability-direct-images.proof.md was also read: this auxiliary weak Chow
statement supports the existing compactification route and changes no blueprint unit.

Hypothesis and clause correspondence:

- The ambient base Spec Z is literally `Spec (CommRingCat.of (ULift.{u} ℤ))`.
  `ULift` places the integer ring in the same universe as the schemes without changing it.
  `universe u` and `set_option autoImplicit false` bind all universe and term variables.
  The ring A and all test schemes use this universe; there is no independently smaller
  test universe that could make a hypothesis vacuous.
- A commutative ring is `(A : Type u) [CommRing A]`. There is no nonzero, domain,
  Noetherian, characteristic, or finiteness assumption on A.
- X is the existing `AlgebraicSpace` over Spec Z. Its map to Spec A is `a`, whose target
  is `schemeSpace (Over.mk (specULiftZIsTerminal.from (Spec (.of A))))`.
  Thus a is an actual morphism of the original sheaves, not a map of point sets.
- The separated hypothesis is `ha_sep : MapIsSeparated a`: this is precisely the
  representable closed-immersion relative diagonal on every scheme test.
- The finite-type hypothesis is `ha_ft : MapIsFiniteType a`: affine-test quasi-compactness
  and local finite type on all compatible representable etale scheme charts. These
  existing predicates are read in AlgebraicSpaceMorphismProperties.lean. Their use adds
  no representability assumption on a.
- The node's convention sentences about quasi-separatedness and finite presentation
  impose no hypotheses on a beyond separated finite type. No finite-presentation
  hypothesis is inserted. Their existing scheme definitions and the chartwise morphism
  interface are imported; there is no second definition of these notions.
- An integer n >= 0 is `n : ℕ`. The projective scheme is the dependency's `ProjectiveSpace`
  with homogeneous-coordinate type `ULift.{u} (Fin (n + 1))`, so n is dimension, not the
  number of homogeneous coordinates. The lift is only a universe adjustment.
- The scheme X' is `X' : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))`; its underlying
  scheme is `X'.left`. Its unique structure morphism over Spec Z supplies exactly the
  ambient-base data required to use its Yoneda algebraic space.
- The source is quasi-compact and separated by `CompactSpace X'.left` and
  `X'.left.IsSeparated`. Mathlib compactness has no Hausdorff requirement here.
  Scheme.IsSeparated means separated over the terminal scheme, agreeing with Spec Z.
- The morphism pi is `π : schemeSpace X' ⟶ X` and its properness is `MapIsProper π`.
  This is separated AND finite type AND closed on point spaces after every
  algebraic-space base change, as stipulated in the node. It is not the representable
  scheme-test properness predicate and does not add representability of pi.
- The actual scheme morphism j has target the specified base-change projective space;
  `IsImmersion j ∧ QuasiCompact j` is its quasi-compact immersion condition.
  Mathlib's IsImmersion.isImmersion_iff_exists was read: it is equivalent to a closed
  immersion followed by an open immersion, exactly the convention in the node.
- The displayed equality `π.hom.hom ≫ a.hom.hom = yoneda.map (Over.homMk ... ...)`
  is a*pi = q*j (composition is written left-to-right in Lean). The scheme morphism
  on the right is `j ≫ (ProjectiveSpace ... ↘ Spec (.of A))`, with the canonical
  projective-space first projection. `specULiftZIsTerminal.hom_ext _ _` merely proves
  that this is a scheme morphism over Spec Z; it changes no map or mathematical data.
  Because X' is quantified with its structure map, this equality also says j is over
  Spec A with source structure map a*pi; no unrelated source map to Spec A is supplied.
- Finally `∀ (W : AlgebraicSpace ...) (w : W ⟶ X), Function.Surjective
  (mapPoint (Limits.pullback.snd π.hom w.hom).hom)` is exactly the point-set surjectivity
  of X' times_X W -> W for every algebraic-space base change. The sheaf pullback is
  the existing Limits.pullback, whose algebraic-space property is supplied by
  fibreProduct_isAlgebraicSpace. W and w are entirely arbitrary, including identity
  and nonrepresentable base changes; surjectivity is not restricted to scheme tests.

Dependency declarations read and used (full signatures and docstrings checked):

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme, Scheme.Hom, Spec, Spec.map.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: AlgebraicGeometry.AlgebraicSpace and its
  IsRepresentableWith / IsAlgebraicSpace interfaces.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers:
  AlgebraicGeometry.AlgebraicSpace.fibreProduct_isAlgebraicSpace (sheaf pullbacks).
- Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology: pointTopologicalSpace, pointImage;
  its Point, PointRepresentative and schemePointMap dependency was also read.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: IsClosedImmersion;
  Mathlib.AlgebraicGeometry.OpenImmersion: IsOpenImmersion;
  Mathlib.AlgebraicGeometry.Morphisms.Immersion: IsImmersion and
  IsImmersion.isImmersion_iff_exists.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: LocallyOfFiniteType;
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact: QuasiCompact;
  Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation: LocallyOfFinitePresentation;
  Mathlib.AlgebraicGeometry.Morphisms.Proper: IsProper and its scheme convention.
- WeilConjectures.AlgebraicGeometry.ProjectiveSpace: ProjectiveSpace and its
  CanonicallyOver instance, whose hom is the first projection of its defining pullback.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties: MapIsLocally,
  MapIsSeparated, MapIsFiniteType, MapIsUniversallyClosed, MapIsProper. Their
  MapIsQuasiCompact and mapPoint definitions in ProperCurveModuli.lean were also read.
- Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite: schemeSpace, whose data is the
  actual representable fppf sheaf, and schemeSheaf_isAlgebraicSpace.
- Mathlib.AlgebraicGeometry.Limits: specULiftZIsTerminal, for the unique ambient map.
- def-weil-size-convention is a metatheoretic convention with no declaration/module;
  it is rendered by explicit universe polymorphism rather than a fabricated object.

The item gains only two existing landed statement-dependency ids:
`def-sfb-space-morphism-properties` and `def-trf-scheme-algebraic-space`. These own the
interfaces used here. All other existing node fields, including the natural-language
statement and proof, are unchanged. No new nodes or dependency modules are needed.

All recorded proof dependency modules available in the read clone are imported with plain
`import`: ProjectiveSpace.AffineImmersion, ChowLemma.ClosedModel, the scheme Etale module,
FlatValuationLifting, ValuativeCriterion, and ReducedClosedSubspaceSupport. The fibre-product
and closed-immersion dependencies are already public statement imports. The atlas,
maximum-degree, configuration, dense-open valuative criterion, qcqs permanence,
closed-subspace properness, and proper-composition nodes have no recorded module in this
snapshot, so no module name is invented for them. None is needed to type this statement.

Edge cases checked before writing:

- Empty X: use the empty scheme and its empty immersion into projective zero-space;
  properness and all pullback surjectivity conditions remain meaningful. There is no
  Nonempty binder on X, X', W, or A's spectrum.
- The zero ring is allowed; its spectrum is empty, reducing to the same case.
- n = 0 gives one homogeneous coordinate and projective zero-space, not empty Proj.
- Identity base change w = identity includes ordinary surjectivity. Empty W imposes
  vacuous surjectivity and is allowed. Arbitrary W is not required to be a scheme.
- The absolute separatedness of X' is justified because projective space over the affine
  base is absolutely separated and an immersion into it is separated. Thus this is the
  same conclusion as the source's H-quasi-projectivity, not an extra source hypothesis.
- Arbitrary u, non-Noetherian rings and positive or zero characteristic are retained.

Searches for an existing theorem or notion:

- msearch.py leanfinder, query: "A separated finite type algebraic space over an affine
  scheme admits a proper universally surjective cover by a scheme with a quasi compact
  immersion in projective space". Eight hits: scheme IsSeparated.hasAffineProperty,
  projective-spectrum properness and separation, isProper_eq, affine-space surjectivity,
  and finite scheme covers. None states the algebraic-space weak Chow lemma.
- msearch.py loogle, query: "AlgebraicGeometry.ProjectiveSpace,
  AlgebraicGeometry.IsProper". Zero hits; ProjectiveSpace is unknown to the Mathlib index.
  The project's actual ProjectiveSpace definition was subsequently opened and used.
- msearch.py grep, query: "weak.?[Cc]how|weak_chow|WeakChow|AlgebraicSpace" in
  Mathlib/AlgebraicGeometry. Zero hits.
- msearch.py leansearch, query: "Weak Chow lemma for algebraic spaces: a separated
  finite type space over an affine scheme has a proper surjective cover by a quasi
  projective scheme". Eight scheme-only properness, separatedness and quasi-separatedness
  hits, including IsProper.toLocallyOfFiniteType; none is the required theorem.
- rg of `weak.?[Cc]how|weak_chow|weakChow|lem-sfb-space-weak-chow` in
  lean/WeilConjectures and lean/Sheaf: no existing statement. Searches for morphism
  properties and scheme-space embeddings found the already-landed definitions named
  above, which are reused rather than restated. No duplicate declaration was introduced.

Validation: scompile.py compiled the delivered module both as its sandbox check and under
its real library module name in 2.2 s and 1.8 s, with no errors or unexpected warnings.
The delivery dry run and final push are performed after this report is written.

No STATEMENT-DISPUTED flag or node fault: the statement agrees with Tag 089J, with its
H-quasi-projectivity unpacked using Tag 01VW and universal surjectivity using Tag 03MH.

## Second reading by Q38

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Maintainer review FIX (2026-10-24)

The universal-surjectivity clause `Function.Surjective (mapPoint (Limits.pullback.snd π.hom w.hom).hom)`
used `AlgebraicSpace.mapPoint`, owned by def-sfb-proper-curve-moduli, which is not a statement
dependency of this item (H2). It is restated as `pointImage (Limits.pullback.snd π.hom w.hom).hom = Set.univ`
with `pointImage` of the stmt_dep def-a1-space-point-topology; the two are equivalent. No other change.
