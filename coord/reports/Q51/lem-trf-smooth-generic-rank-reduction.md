## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothGenericRankReduction` states
`AlgebraicGeometry.Scheme.Modules.exists_admissibleBlowup_smooth_genericRankReduction`.
Its sole proof is `sorry`. There are no new definitions, additional nodes, dependency
repairs or statement changes. The docstring carries all nine proof steps of the DAG node,
including the cited helper nodes. The source is `literature/stacks-project/flat.tex`,
Tag 0815 (`theorem-flatten-module`, third proof paragraph) and Tag 0811
(`lemma-flatten-module-pre`), both opened and read.

Hypothesis correspondence:

- Schemes: `{X S : Scheme.{u}}`, with `[IsAffine S]` for the affine base.
- Nonnegative relative dimension: `n : ℕ`.
- The specified affine smooth family: `f : X ⟶ S`, `[IsAffineHom f]` and
  `[SmoothOfRelativeDimension n f]`. The last class includes smoothness.
- Geometrically integral fibres after every residue-field extension:
  `[GeometricallyIntegral f]`, Mathlib's condition that every field-valued base
  change is integral, equivalently that all residue-field fibres are geometrically integral.
- The given module: `F : X.Modules`, `[F.IsQuasicoherent]` and `[F.IsFiniteType]`.
- The preserved quasi-compact open: `U : S.Opens`, `hU : IsCompact (U : Set S)`.
- Finite presentation over that open: `hfp` on `F.restrict (f ⁻¹ᵁ U).ι`.
- Flatness over that open: `hflat` on the same module, relative to `f ∣_ U`,
  using the recorded affine-section predicate `Scheme.Modules.IsFlatOver`.

Conclusion correspondence:

- `B : IsAdmissible S U` retains the centre `B.I`, finite type and disjointness
  from `U`. Take `T = B.I.blowup` and `b = B.I.blowupMap`; the identification
  with the blowup is the identity. This canonical model loses none of the
  existential statement, which is invariant under isomorphism over `S`.
- `m : ℕ`, `V : Fin m → B.I.blowup.Opens`, `(⨆ a, V a) = ⊤` and
  `∀ a, IsAffineOpen (V a)` give the finite affine open covering `T_a`.
- Put `q = pullback.snd f B.I.blowupMap`. The chart source is
  `(q ⁻¹ᵁ V a).toScheme`. By Mathlib's `isPullback_morphismRestrict`, this is
  precisely the inverse-image open model of `X ×_S T_a`.
- The existential names `g`, `G`, `Ua` are constrained by three equalities:
  `g = q ∣_ V a`, `G = (moduleStrictTransform f B.I F).restrict (q ⁻¹ᵁ V a).ι`
  (with the explicit finite-type proof), and
  `Ua = (V a).ι ⁻¹ᵁ (B.I.blowupMap ⁻¹ᵁ U)`.
  Thus these are the actual family, strict-transform restriction `F_a`, and
  `T_a ∩ b⁻¹(U)`; no map or module is left unconstrained. These equalities
  name canonical expressions without introducing private copies or signature lets.
- `IsAffineHom g ∧ SmoothOfRelativeDimension n g ∧ GeometricallyIntegral g`
  records all family permanence clauses.
- `IsCompact (Ua : Set (V a).toScheme)` is the required quasi-compactness.
- `G.IsQuasicoherent ∧ G.IsFiniteType` and the two properties on
  `G.restrict (g ⁻¹ᵁ Ua).ι` are exactly finite presentation and flatness over `Ua`.
- `r : ℕ` and `α : SheafOfModules.free (ULift.{u} (Fin r)) ⟶ G` give
  `O_{X_a}^{⊕ r_a} → F_a`. The ring parameter is explicitly the chart's
  structure sheaf. The universe lift preserves the number of basis vectors.
- `W` is an open of the chart source, `Surjective (W.ι ≫ g)` says it surjects
  onto `T_a`, and `IsIso ((restrictFunctor W.ι).map α)` is the stated local
  isomorphism of this same map.
- `H_a` is exactly `cokernel α` everywhere, with quotient arrow `cokernel.π α`.
  `ShortComplex.mk α (cokernel.π α) (cokernel.condition α) |>.ShortExact`
  expresses the original sequence including injectivity and surjectivity.
- For every `T' : Scheme.{u}` and `t' : T' ⟶ (V a).toScheme`, the same two
  arrows are pulled back by `tensorPullback (pullback.fst g t')` and required
  to form a `ShortExact` short complex. The existential `w` only supplies
  the zero-composite proof. Thus exactness holds for every scheme base change,
  including identity and empty tests, and for the actual tensor-pulled quotient map.
- `(cokernel α).IsQuasicoherent ∧ (cokernel α).IsFiniteType` records both
  cokernel properties. Restriction via `restrictFunctor (g ⁻¹ᵁ Ua).ι` has
  `IsFinitePresentation` and `IsFlatOver (g ∣_ Ua)` as required.
- At every `t : T_a`, the fibre module is
  `(tensorPullback (g.fiberι t)).obj (cokernel α)`. Its support is the subtype
  `{x : g.fiber t | ¬ Subsingleton (...presheaf.stalk x)}` with subspace topology.
  `topologicalKrullDim` of this support is required to be `< (n : WithBot ℕ∞)`.
  For nonempty support this means dimension at most `n - 1`. For empty support
  Mathlib assigns bottom rather than -1; both give exactly the stated inequality
  for every natural `n`. This avoids truncated natural subtraction at `n = 0`.
- The explicit final implication `n = 0 → ∀ t, IsZero (...)` also records the
  node's stated zero-fibre consequence, including the endpoint case.

Dependency declarations read and used (all statement dependencies):

| Node | Module | Declarations used |
| --- | --- | --- |
| def-sbc-smooth-morphisms | Mathlib.AlgebraicGeometry.Morphisms.Smooth | SmoothOfRelativeDimension |
| def-kun-topological-krull-dimension | Mathlib.Topology.KrullDimension | topologicalKrullDim |
| def-pc-module-pullback | Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction | tensorPullback, publicly imported from WeilConjectures.AlgebraicGeometry.TensorPullback |
| def-weil-pbc-scheme-conventions | convention record, no module | Scheme, IsAffine, IsAffineHom, IsAffineOpen, Surjective, Opens and scheme fibre products |
| def-weil-quasi-separated-morphism | Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated | QuasiSeparated; publicly imported for the conventions, no extra hypothesis imposed |
| pqf-def-coherent | Sheaf.AlgebraicGeometry.CoherentFiniteType | exposed IsQuasicoherent and IsFiniteType, the components of IsQuasiCoherentFiniteType |
| def-weil-pbc-module-finite-type-presentation | Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators and Quasicoherent | IsFiniteType, IsFinitePresentation |
| def-pc-scheme-module-flat-over | WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic | Scheme.Modules.IsFlatOver |
| def-nagata-admissible-blowup | WeilConjectures.Blowup.AdmissibleBlowup | IsAdmissible, its I, finiteType and disjoint_support fields |
| def-trf-module-strict-transform | Sheaf.AlgebraicGeometry.ModuleStrictTransform | moduleStrictTransform |

The finite-type proof for the retained ideal uses
`Scheme.IdealSheafData.isFiniteType_toModules_sheaf` from
`WeilConjectures.AlgebraicGeometry.FiniteTypeIdealModule`. Geometric integrality
uses Mathlib's existing `GeometricallyIntegral` and its documented fibre
characterization. Exactness uses `CategoryTheory.ShortComplex.ShortExact`.
All already stated proof dependencies are imported as plain `import`, retaining
upstream modules in preference to retired duplicates. The proof-only node
`lem-trf-generic-rank-admissible-invariance` has no declaration on the read base,
so has no import; it is not needed to type this statement. The maintainer can
add its proof import after it is stated. No import cycle was introduced by the
successful compilation.

Edge cases checked before writing: `n = 0` (strict dimension bound forces empty
support, and explicit zero-fibre clause is present); `r = 0` (empty lifted basis);
`F = 0`; `U = ∅` (the zero-centre blowup can be empty); `U = S` (a unit
centre is admissible, so this gives local generic subtraction without modifying
that open); empty `S` and `T` (the empty cover `Fin 0` is allowed); disconnected
bases (ranks chosen per chart rather than a single global rank); arbitrary
characteristic; arbitrary base changes, including nonflat and nonaffine ones.
No Noetherian or global finite-presentation hypothesis on `F` was added.

Searches for an existing statement:

- `msearch.py ... leanfinder` with the query “For a smooth affine family with
  geometrically integral fibres an admissible blowup locally admits a universally
  injective free module map whose cokernel has strictly smaller fibre support
  dimension”: 8 hits, including standard smooth algebras, smooth relative
  dimension, universally injective scheme morphisms and the smooth locus.
  None gives an admissible module blowup or universally exact subtraction.
- `msearch.py ... leansearch` with “A smooth affine family with geometrically
  integral fibres admits after an admissible blowup a local universally exact
  free subtraction with smaller fibre support”: 8 smoothness/class-constructor
  hits, none the statement.
- `msearch.py ... loogle` with
  `AlgebraicGeometry.SmoothOfRelativeDimension, SheafOfModules.IsFiniteType`:
  0 hits.
- `msearch.py ... grep` with `generic.*(basis|rank)|universally.*injective|flattening`
  in Mathlib `AlgebraicGeometry`: 13 hits, on relative gluing, quasi-finite
  morphisms, flat descent and universally injective scheme morphisms; no match.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for generic rank reduction,
  generic free blowups, smaller support and free subtraction, plus the exact node
  id in `lean/WeilConjectures`: no existing declaration of this statement.
  `GenericFreeBlowup` provides only the preliminary free locus;
  `FlatteningModuleByAdmissibleBlowup` states the final flattening theorem;
  `SmoothTopDimensionRankDecomposition.exists_smoothTopDimension_rank_decomposition`
  describes rank-labelled subterminal sheaves and requires finite presentation
  of the original module. It does not state this reduction lemma.
- Searched `dag/lean_names_upstream.json` for the planned name: no clash.
  Existing declaration sources and docstrings were opened rather than trusting
  search names alone.

No statement dispute or node fault was found. The initial compile identified
only a dot-notation resolution issue for `cokernel α` (its inferred type was
`SheafOfModules`); explicit `restrictFunctor` applications repair it without
changing any objects or hypotheses.

## Second reading by Q51

This is a second pass by the assigned worker; the dispatcher prohibits starting
another agent, and the maintainer provides the independent review. I reopened
the node and the full Lean statement and checked each hypothesis and conclusion
against the correspondence above. The equalities fixing `g`, `G` and `Ua`
ensure these witnesses cannot replace the original canonical data. The centre
used in `moduleStrictTransform` is the same `B.I` used for the admissible
blowup. `W` surjects onto the whole affine chart. Universal exactness pulls back
both actual arrows; the cokernel is not an arbitrary module. Cokernel finite
presentation and relative flatness are asserted only over `Ua`. Support is
computed on the tensor-pulled fibre module, not the original stalk on the total
space. The strict bound includes the dimension-zero case, and the final clause
makes zero fibre modules explicit. The cover can be empty and no rank is
required to be positive. The only change on this rereading was to write the two
cokernel restrictions explicitly for Lean's field-notation resolution. No
mathematical mismatch remained and the node statement is unchanged.
