## Worker report

The delivery states `AlgebraicGeometry.Scheme.Modules.exists_admissibleBlowup_fiberwise_finiteLocallyFree`
in `Sheaf.AlgebraicGeometry.GenericFreeBlowup`. Its only theorem proof is `sorry`; it introduces
no definitions, auxiliary assertions, or new nodes. The statement is unchanged. I read the
source `literature/stacks-project/flat.tex`, `lemma-flatten-module-pre` (Tag 0811), lines
8781–8846, including all four hypotheses and the two conclusions, and the node's expanded
nine-step proof. The theorem docstring records that proof and its cited nodes.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node | Lean |
| --- | --- |
| Schemes S and X and morphism f | `{X S : Scheme.{u}}`, `(f : X ⟶ S)` |
| S quasi-compact | `[CompactSpace S]` (quasi-compactness, no Hausdorff condition) |
| S quasi-separated | `[QuasiSeparatedSpace S]` |
| f affine | `[IsAffineHom f]` |
| f flat | `[Flat f]` |
| f of finite presentation | `[LocallyOfFinitePresentation f]`, together with the quasi-compactness and quasi-separatedness already implied by `[IsAffineHom f]`; this is exactly Stacks 01TP |
| F an O_X-module | `(F : X.Modules)` |
| F quasi-coherent | `[F.IsQuasicoherent]` |
| F of finite type | `[F.IsFiniteType]` |
| Every fibre integral after every field extension | `hgeom : ∀ s : S, GeometricallyIntegral (f.fiberToSpecResidueField s)` |
| U a quasi-compact open of S | `(U : S.Opens)` and `hU : IsCompact (U : Set S)` |
| F on X_U of finite presentation | `hfp : (F.restrict (f ⁻¹ᵁ U).ι).IsFinitePresentation` |
| F flat over S at the generic point of each fibre over U | `hflat` quantifies over `s ∈ U` and `ξ : f.fiber s` with `IsGenericPoint ξ Set.univ`; it asserts `Module.Flat` for the original stalk `F.presheaf.stalk (f.fiberι s ξ)`, with base local-ring action `Module.compHom _ (f.stalkMap (f.fiberι s ξ)).hom` |
| A U-admissible blowup b | `∃ B : IsAdmissible S U`; its actual source is `B.I.blowup`, and b is `B.I.blowupMap` |
| An open V in X ×_S S^b | `∃ V : (Limits.pullback f B.I.blowupMap).Opens` |
| V → S^b surjective | `Surjective (V.ι ≫ pullback.snd f B.I.blowupMap)` |
| Strict transform for the same centre, restricted to V | `(@moduleStrictTransform X S f B.I ... F inferInstance).restrict V.ι` |
| This restriction finite locally free, allowing variable finite rank | `SheafOfModules.IsFiniteLocallyFree` of that restriction, not the constant-rank predicate |

The restriction to `f ⁻¹ᵁ U` is the open-subscheme realization of X_U, canonically isomorphic
to the pullback along U. For `hflat`, `f (f.fiberι s ξ) = s` by the fibre square; using the
actual image point gives the canonical base local ring without an arbitrary equality cast.
Integral fibres have a unique generic point, so universal quantification over all generic
points means precisely the node's generic-point condition. It neither assumes global
relative flatness of F nor replaces the original stalk by the fibre module stalk.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom` (locally ringed spaces and their morphisms).
- `pqf-def-coherent`: `WeilConjectures.AlgebraicGeometry.Coherent`, whose current source was
  read with `scompile.py --source`. It explicitly reuses Mathlib's `IsQuasicoherent` and
  `IsFiniteType`; those are the two notions this statement uses. Coherence is not assumed.
- `def-pc-scheme-module-flat-over`: `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`,
  `AlgebraicGeometry.Scheme.Modules.IsFlatOver`. Its full signature and docstring state
  affine-local relative flatness and the equivalent stalkwise condition. Here only the
  stalkwise condition at the specified points is imposed, explicitly using `Module.Flat`
  and the canonical restricted scalar structure; the global predicate would be stronger.
- `def-weil-pbc-module-finite-type-presentation`: `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`
  and `.Quasicoherent`, `SheafOfModules.IsFiniteType` and `IsFinitePresentation`.
- `def-weil-pbc-scheme-conventions`: this is a convention record with no declaration or module;
  use its Mathlib meanings `Flat`, `IsAffineHom`, `LocallyOfFinitePresentation`, `Surjective`,
  `CompactSpace`, and `QuasiSeparatedSpace` directly.
- `def-nagata-admissible-blowup`: `WeilConjectures.Blowup.AdmissibleBlowup`,
  `AlgebraicGeometry.IsAdmissible`. Its fields retain the ideal, finite type and
  `Disjoint U I.support`. Using its canonical blowup realizes the existential blowup datum
  of the node with identity identification; any datum with a specified isomorphism can be
  transported to this representative. No arbitrary morphism replaces the blowup.
- `def-trf-module-strict-transform`: `Sheaf.AlgebraicGeometry.ModuleStrictTransform`,
  `AlgebraicGeometry.Scheme.Modules.moduleStrictTransform`. Read all four declarations in
  that file: complementary open, restriction map, kernel and cokernel. This is the actual
  quotient by sections vanishing off the exceptional set, using tensor pullback, with the
  centre retained.
- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsIntegral`;
  used through `Mathlib.AlgebraicGeometry.Geometrically.Integral`, `GeometricallyIntegral`.
  Its docstring and field quantify over every field-valued base change, and its fibre
  equivalence is `GeometricallyIntegral.iff_geometricallyIntegral_fiber`.
- `def-pc-scheme-fibre`: `Mathlib.AlgebraicGeometry.Fiber`, `Scheme.Hom.fiber`, `fiberι`,
  `fiberToSpecResidueField`; read the definitions as the actual residue-field pullback.
- `def-sc-generic-point`: the Mathlib leaf `Mathlib.Topology.Sober`, `IsGenericPoint`,
  defined by `closure {ξ} = Set.univ` here. No lean record is required for this leaf.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`, `Scheme.residueField`,
  the local-ring residue field, implicit in the fibre construction and structure map.

The only additional statement dependency is the already landed
`lem-pqf-finite-type-ideal-module`, module `Sheaf.AlgebraicGeometry.FiniteTypeIdealModule`,
declaration `Scheme.IdealSheafData.isFiniteType_toModules_sheaf`. I read its full statement,
source and proof. It converts `B.finiteType : B.I.ofFiniteType` into the proof argument
`B.I.toModules.IsFiniteType` required by the strict-transform definition. This uses the
existing bridge rather than imposing a second finite-type hypothesis or duplicating it.
The item gains that id in `stmt_deps`; no field of any dependency node changes.

The modules of all proof dependencies with a recorded declaration are imported. Shared
modules are imported once; the unstated proof nodes have no module to import. The proof
plan imports include `BoundaryPreparation`, `Blowup.Density`, `Blowup.Principalization`,
`IdealSheaf.EffectiveCartier`, `IdealSheaf.Invertible`, `QuasicoherentFiniteTypeAffine`,
`Blowup.Extension`, and `LocalizedModule.Basic`. The other recorded proof dependencies
are already public imports for the statement. There is no import cycle.

Edge cases checked mathematically:

- Empty S: every pointwise premise is vacuous, the canonical blowup is empty, and V may be
  empty; surjectivity onto an empty base is allowed. No `Nonempty S` was inserted.
- Empty U: neither finite presentation on the empty open nor generic flatness over U
  restricts F. The zero ideal is admissible and its blowup is empty, as in the source's
  density reduction. The conclusion permits this case.
- U = S: admissibility makes the centre the unit ideal and the blowup the identity. Finite
  presentation and relative generic flatness give the fibrewise nonempty free locus used
  in the rank argument; no modification on U is introduced.
- Zero F and rank zero are included. `IsFiniteLocallyFree` permits the empty free basis.
  Disconnected bases and different ranks on different pieces are not excluded.
- Geometric integrality means nonempty integral after every field extension, rather than
  just ordinary integrality or integrality after one chosen closure. The standard Mathlib
  same-universe geometric predicate has no independent smaller universe for test fields.
- S need not be reduced, integral, Noetherian or separated. No such condition is bound.
  V need not be quasi-compact. No requirement says it contains the whole inverse image of U.

Searches performed before writing (all via the authorized wrapper where applicable):

1. `msearch.py ... leanfinder "scheme affine flat finite presentation geometrically integral fibres strict transform finite locally free admissible blowup"`: eight hits, including `Flat`, `IsIntegralHom`, `LocallyOfFinitePresentation`, `UniversallyOpen.of_flat`, normalization and smooth relative dimension; no flattening/strict-transform theorem.
2. `msearch.py ... leansearch "admissible blowup strict transform finite locally free on a fibrewise nonempty open"`: eight hits about properness, local finite presentation, finite morphisms and local freeness; no exact theorem.
3. `msearch.py ... loogle "IsAdmissible, moduleStrictTransform, IsFiniteLocallyFree, IsIntegral, IsFlatOver"`: zero hits, unknown identifier `IsAdmissible` in the external index. A separate quoted `"IsFiniteLocallyFree"` query returned zero hits. The actual upstream declarations were found and read locally instead.
4. `msearch.py ... grep "strictTransform|generic.*[Ff]ree|flatten" AlgebraicGeometry`: zero Mathlib hits.
5. `rg` of Mathlib's AlgebraicGeometry and of the source `WeilConjectures` and project
   `lean/Sheaf` for `GenericFreeBlowup|exists_admissibleBlowup_fiberwise_finiteLocallyFree|flatten.module.pre|0811|lem-trf-generic-free-blowup`, and upstream names JSON: no exact theorem or name collision.
6. Broader `rg` of `IsAdmissible`, `moduleStrictTransform`, `IsFlatOver`, `IsFiniteLocallyFree`
   and finite-type ideal/module bridges found the precise reusable declarations listed above.
   In particular upstream `AdmissibleBlowup.lean` explains why it has no module-flattening
   statements; the side project's strict transform is used rather than rewritten.

No statement dispute, correction, dependency repair or new definition was necessary.
The clean compile used only `scompile.py N0 lem-trf-generic-free-blowup` and compiled this
file separately, both as the sandbox test and under its final module name, without errors
or warnings. The first compile exposed a namespace collision with `Modules.pullback` and
an invalid line break after field notation; both were corrected before recording the node.

## Second reading by N0

Author's explicit second pass, not an independent-worker review; the dispatch brief requires
self-delivery and reserves independent review for the maintainer. I reopened the source,
node and final file and compared the rows above to the Lean signature. The base has exactly
qcqs; f has exactly affine, flat and finite presentation; F has exactly quasi-coherence,
finite type and finite presentation on X_U. `hflat` uses the original module at images of
fibre generic points, with scalar action through f, and only for s in U. `hgeom` tests
geometric integrality of each residue-field fibre. The two existential witnesses are the
actual canonical blowup of the retained admissible ideal and an actual open of its base
change. Both conclusions refer to that same ideal, and surjectivity is of the restriction
of the second projection. Variable rank and rank zero are retained. No hypothesis or
conclusion mismatch was found. The two compile fixes changed only name resolution and
syntax, not the statement's mathematics. The finite-type bridge removes the need to add
any redundant finite-type condition on the chosen centre. The node record signature is
copied directly from the final file; only `lean` and the one landed bridge dependency change.
