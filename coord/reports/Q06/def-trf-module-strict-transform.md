## Worker report

Repaired the returned stage-2 delivery ae92188f8b66. The sandbox supplied to this
repair contained no retained Lean module, node copy, or report; this packet was
reconstructed from the current shared node and the return's explicit findings.
The delivery wrapper rebases the packet on current newtargets-dag. The only node
field changed is `lean`; in particular, the base's `split_report` is preserved
unchanged, with no new stage-1 split_report delta.

The new module `Sheaf.AlgebraicGeometry.ModuleStrictTransform` defines the actual
module quotient in Stacks Project, divisors.tex, Definition
`definition-strict-transform`, Tag 080D (1), lines 8751–8797 of the local source.
The blueprint association is `def-trf-module-strict-transform`, serving the
flattening input to `lem-trf-local-term-locality` in sec-trace-formula,
sk-i-curve-zero (main-20261015). Every definition and the module carry source
and blueprint docstrings. No theorem, new axiom, or `sorry` was added.

Hypotheses and clauses, with names below in `AlgebraicGeometry.Scheme.Modules`:

| Node text | Lean rendering |
| --- | --- |
| Schemes X and S and morphism f:X→S | `{X S : Scheme.{u}} (f : X ⟶ S)`; u is explicitly declared and arbitrary. |
| Finite-type quasi-coherent centre I⊆O_S | `(I : S.IdealSheafData) [I.toModules.IsFiniteType]`. IdealSheafData is Mathlib's quasi-coherent ideal, and its canonical associated ideal module is of finite type. No noetherian, properness, quasi-compactness, or flatness assumption is imposed. |
| b:Sᵇ=Bl_I(S)→S | The recorded `I.blowup` and `I.blowupMap` from `WeilConjectures.Blowup.Gluing`. |
| E=b⁻¹V(I) | V(I) is `I.support`; E is used through its complementary open, so no extra scheme structure is invented. |
| Y=X×_S Sᵇ and projections p and q | `Limits.pullback f I.blowupMap`, `pullback.fst f I.blowupMap`, and `pullback.snd f I.blowupMap`. |
| Complement of q⁻¹E | `moduleStrictTransformOpen f I := (pullback.snd f I.blowupMap ≫ I.blowupMap) ⁻¹ᵁ I.support.compl`. Inverse image of the complement equals complement of the inverse image. |
| Quasi-coherent O_X-module F | `(F : X.Modules) [F.IsQuasicoherent]` in the main definition. |
| p*F=O_Y⊗_(p⁻¹O_X)p⁻¹F | `(tensorPullback (pullback.fst f I.blowupMap)).obj F`; this is the recorded tensor-formula pullback, never Mathlib's different `Modules.pullback`. |
| Restriction to the complement | `moduleStrictTransformRestriction f I F`, the unit of Mathlib's `restrictAdjunction` for the open immersion. It maps p*F to j_*j^*(p*F). |
| K is the subsheaf of local sections restricting to zero | `moduleStrictTransformKernel f I F := kernel (moduleStrictTransformRestriction f I F)`. The kernel inclusion is `kernel.ι` of that same map. |
| Fᵇ=p*F/K | `moduleStrictTransform f I F := cokernel (kernel.ι (moduleStrictTransformRestriction f I F))`. This is the quotient in the abelian category of sheaves of O_Y-modules, not a presheaf quotient. |
| Retain I, not merely b | I is an explicit argument of all four definitions and supplies both the blowup and the complementary open. |

The first three definitions expose the ingredients of this one construction;
they need no quasi-coherence or finite-type hypotheses to construct their data.
The main definition has exactly the node's finite-type and quasi-coherence
hypotheses. `moduleStrictTransformKernel` is definitionally the domain of the
kernel inclusion whose cokernel defines the quotient.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `.Hom` from
  `Mathlib.AlgebraicGeometry.Scheme`, available through the public imports.
- `pqf-def-coherent`: `WeilConjectures.AlgebraicGeometry.Coherent` explains the
  three recorded notions. Its quasi-coherent and finite-type notions are
  Mathlib's `SheafOfModules.IsQuasicoherent` and `.IsFiniteType`, used here;
  `RingedSpace.IsCoherent` is the stronger coherent notion and is not imposed.
  Read this module through `scompile.py --source` because the older checkout
  lacks the current file.
- `def-nagata-global-blowup`: `Scheme.IdealSheafData.blowup` from
  `WeilConjectures.Blowup.Gluing`, and its `blowupMap`.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `.fst`, `.snd` from
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`; existence is
  provided by `Mathlib.AlgebraicGeometry.Pullbacks`.
- `def-pc-module-pullback`: `Scheme.Modules.tensorPullback` from
  `WeilConjectures.AlgebraicGeometry.TensorPullback`, read in full through
  `scompile.py --source`. Its obj is extension of scalars on the actual inverse
  image, followed by sheafification.

Additional existing API: `Scheme.IdealSheafData.toModules` from
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`, the kernel ideal
module; `Scheme.Modules.restrictAdjunction` and its section formula
`restrictAdjunction_unit_app_app` in `Mathlib.AlgebraicGeometry.Modules.Sheaf`.
That formula identifies the unit on V with restriction to the image of j⁻¹(V),
which for this inclusion is exactly V∩(q⁻¹E)ᶜ. Kernels of module sheaves are
sectionwise kernels; cokernels are sheaf cokernels. Thus the categorical
construction has precisely the required local-section meaning.

Edge cases checked against the construction and Tag 080D: F=0 gives zero;
an empty base or source causes no nonempty assumption; I=O_S has empty support,
so the complement is all of Y, K=0, and the quotient is p*F; I=0 has blowup
empty, yielding the unique module there. More generally if all of Y lies over
the exceptional locus, restriction is to the empty open, K=p*F, and the quotient
is zero. For S=Spec k[t], I=(t), f=id and
F=O_S⊕(O_S/(t)), the blowup is S and the kernel is the t-power torsion summand,
so the quotient is O_S. There is no characteristic restriction.

Searches for an existing definition (2026-10-17 UTC, recorded in sandbox
searches.jsonl):

- `msearch.py ... leanfinder "strict transform quasi coherent module quotient pullback by sections supported on exceptional divisor"`: eight hits, including tilde, restriction and ideal sheaf maps; no module strict transform.
- `msearch.py ... leansearch "strict transform of quasi coherent module under blowup"`: eight hits, including quasi-coherence and restriction stalk comparisons; none defines this quotient.
- `msearch.py ... loogle "strictTransform, SheafOfModules, kernel"`: no hits, unknown identifier strictTransform.
- `msearch.py ... grep "strictTransform|strict_transform|strict transform"`: no Mathlib hits.
- `rg` of the same strict-transform expressions in the upstream WeilConjectures source and side `lean/Sheaf`: scheme strict transforms and their maps/opens, and affine module torsion, exist; the sheaf quotient does not. The exact item-id search in upstream gave no hit.
- `rg` for the four proposed declaration names in upstream, side Lean and dag/lean_names_upstream.json gave no hit. Existing supported étale section constructions concern different categories, not this Zariski module quotient.

Return points repaired: H1 now has a real Lean module and this Worker report
plus the Second reading section below; H2 now has a complete lean record,
including all four declarations and the main signature copied verbatim from
the file, with no split_report change; H4 is resolved by using the actual
scheme, ideal, blowup, fibre-product and tensor-pullback interfaces rather than
misidentifying the scheme strict transform with a module quotient.

## Second reading by Q06

This is a second pass by the same worker, not a claim of an independent agent
review; the brief forbids starting agents and the maintainer independently
reviews the delivered immutable head. Reopened the node, Stacks definition and
all four Lean definitions together.

The main binders retain arbitrary X,S,f, the actual centre I, finite type of its
associated ideal module, and quasi-coherence of F. No property of f or of S was
added. In the helper open, q followed by b pulls back S\V(I), which is precisely
the complement of q⁻¹E. The restriction arrow is the canonical adjunction unit,
not an arbitrary map. Its kernel K selects exactly the sections vanishing on
that intersection, and the main definition takes the cokernel of that kernel's
inclusion, hence the required sheaf quotient. It uses tensorPullback for p*F;
the geometric fibre product has been qualified as Limits.pullback to avoid the
unrelated module-pullback name. The first compile detected that namespace
collision; it was corrected before delivery. The source's note about dependence
on the centre is respected by the explicit I argument. All zero, empty-open,
empty-scheme, unit-centre and zero-centre cases remain included.

No source/node correction or new/dependency node was necessary. The base's
stage-1 fields and statement dependencies remain unchanged. All four helper and
main declarations have Tag 080D source/blueprint docstrings. The node's
lean.statement is extracted directly from the main def signature. Compilation
and the prescribed delivery dry run are recorded by the delivery tools.
