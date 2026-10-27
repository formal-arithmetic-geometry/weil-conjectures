## Worker report

The module `Sheaf.AlgebraicGeometry.CanonicalAffineChartsQcOpenImmersion` states
`AlgebraicGeometry.isOpenImmersion_and_quasiCompact_of_canonical_affine_charts`.
Its only proof is `sorry`; it introduces no definitions or auxiliary theorems.
Only the item's `lean` record changes. No statement correction, dependency repair,
new node, or disputed statement is needed. No repair note exists for this item.

Source read: `literature/stacks-project/morphisms.tex`,
`lemma-characterize-quasi-affine` (Tag 01SM), lines 2224–2278, especially the final
sentences of (2) implies (4). The node extracts the chart-to-global argument:
the chart identifications are explicit hypotheses rather than constructing a
relative spectrum again.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Schemes X, Y, S, with no size restriction beyond the standard category of schemes | `{X Y S : Scheme.{u}}`, with explicit arbitrary `universe u` |
| Morphisms f, π, c | `(f : X ⟶ S) (π : Y ⟶ S) (c : X ⟶ Y)` |
| π composed with c equals f | `(hc : c ≫ π = f)`; category composition is left to right |
| π affine | `[IsAffineHom π]` |
| Every affine open U of S | Both `hqa` and `hcharts` quantify `∀ U : S.Opens, IsAffineOpen U → ...` |
| X_U and Y_U are inverse-image open subschemes | `(f ⁻¹ᵁ U).toScheme` and `(π ⁻¹ᵁ U).toScheme` |
| X_U quasi-affine in the compact convention | `hqa` asserts `(f ⁻¹ᵁ U).toScheme.IsQuasiAffine` |
| Chart isomorphism Y_U ≅ Spec Γ(X_U, O) for each affine U | `hcharts` gives `∃ h : (π ⁻¹ᵁ U).toScheme ≅ Spec Γ((f ⁻¹ᵁ U).toScheme, ⊤), ...` |
| c_U is the restriction of c | `c.resLE (π ⁻¹ᵁ U) (f ⁻¹ᵁ U) ...` |
| h_U composed with c_U is j_X_U | The equality `c.resLE ... ≫ h.hom = (f ⁻¹ᵁ U).toScheme.toSpecΓ` |
| j corresponds to the identity on global sections | `Scheme.toSpecΓ` is defined as the unit of `ΓSpec.adjunction` |
| c is an open immersion | First conjunct `IsOpenImmersion c` |
| c is quasi-compact as a morphism | Second conjunct `QuasiCompact c` |
| No compactness or separation condition on S | No such binder, instance, or condition occurs |

The restriction's containment proof is
`(congrArg (fun g : X ⟶ S ↦ g ⁻¹ᵁ U) hc).symm.le`.
It is precisely the inequality obtained from `c⁻¹(π⁻¹(U)) = f⁻¹(U)`;
preimage of a composite is definitionally iterated preimage. Thus `resLE`
has exactly the source and target named in the node, and no arbitrary local
map or extra hypothesis replaces the restriction. Its identity
`Scheme.Hom.resLE_comp_ι` identifies the composite with the open inclusion
as the restriction of `c`.

Mathlib's `Scheme.IsQuasiAffine` extends `CompactSpace` and
`IsImmersion X.toSpecΓ`; it gives an open immersion of `X.toSpecΓ`.
This is exactly the node's convention: the forward direction from a compact
open embedding into an affine scheme is `IsQuasiAffine.of_isImmersion`,
using the affine scheme's quasi-affineness; the reverse direction uses the
canonical open immersion into `Spec Γ(X, ⊤)` and the class's compactness.
In particular the hypothesis does not mean a possibly noncompact open
subscheme, and does not assume a globally quasi-affine X.

Dependency declarations inspected and used (all recorded matches are usable):

| Node | Module and declarations |
| --- | --- |
| def-pc-scheme | `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom` |
| pqf-def-affine-morphism | `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `AlgebraicGeometry.IsAffineHom` |
| lem-weil-pbc-morphism-into-affine-scheme | `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`: `ΓSpec.adjunction`, `Scheme.toSpecΓ`; the recorded basic-open clause `Scheme.preimage_basicOpen` in Scheme was also read |
| def-weil-open-immersion | `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion` |
| def-weil-finite-type-morphism | `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`; its recorded quasi-compact component is `AlgebraicGeometry.QuasiCompact` in `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` |
| def-weil-affine-spectrum | `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map` |
| lem-trf-quasi-affine-canonical-affine-embedding | `Mathlib.AlgebraicGeometry.QuasiAffine`: `Scheme.IsQuasiAffine`, its compactness projection and separatedness/open-immersion instances, `Scheme.IsQuasiAffine.of_isImmersion` |
| lem-weil-pbc-open-immersion-injective-local-source | `Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion`: `IsOpenImmersion.of_forall_source_exists` |
| lem-weil-pbc-affine-scheme-qcqs | `Mathlib.AlgebraicGeometry.AffineScheme`: `Scheme.compactSpace_of_isAffine`; `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`: `quasiSeparatedSpace_of_isAffine` |
| lem-weil-pbc-qcqs-morphism-permanence | `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`: `quasiCompact_of_compactSpace`, the component used in this node's proof |
| lem-pc-quasi-compact-local-on-target | `Mathlib.AlgebraicGeometry.Morphisms.Basic`: `IsZariskiLocalAtTarget.of_iSup_eq_top` |

The last proof-only modules are imported without `public`; modules needed to
state the notions are public imports. The restriction construction is the
existing `Scheme.Hom.resLE` in `Mathlib.AlgebraicGeometry.Restrict`.
The docstring gives all five proof steps, including global injectivity and the
fact that quasi-separatedness is used only on the affine target charts.

Edge cases checked mathematically before writing:

- Empty S: a morphism to S forces X and Y empty; the empty map has both
  conclusions. The quantifiers include the empty affine open.
- Empty X with nonempty base: each chart is the empty quasi-affine scheme;
  when the required chart isomorphisms exist they force Y's charts empty.
  No nonemptiness assumption appears.
- Non-separated S, or a base admitting no finite affine cover: the proof
  uses an arbitrary affine cover and target locality. There is no finite
  cover, compactness, separatedness, or quasi-separatedness hypothesis on S.
- A compact nonaffine quasi-affine chart, such as punctured affine two-space
  over a field: `IsQuasiAffine` permits it; no `IsAffine X_U` is imposed.
- Chart isomorphisms need not be chosen compatibly: each is existential for
  its U, and only its equality with the canonical restriction is used.
- No field, characteristic, reducedness, finite type, or Noetherian binder
  is present. The schemes can be over arbitrary rings.

Searches made with the prescribed `msearch.py` wrapper (Q38, this item):

- LeanFinder: “A morphism over a base with canonical quasi affine affinization
  maps on every affine base chart is a quasi compact open immersion”. Eight
  hits: `IsQuasiAffine.of_isImmersion`, `.of_isAffineHom`, the two affine-test
  quasi-compactness characterizations, the canonical open immersion instance,
  and general immersion tools. None states this relative chart criterion.
- Loogle: `AlgebraicGeometry.IsOpenImmersion, AlgebraicGeometry.QuasiCompact`.
  Twelve hits on ideal sheaves, normalization, immersion factorization,
  Noetherian targets and fpqc descent; none is the node's statement.
- LeanSearch: “Canonical affine charts of a quasi affine scheme give a quasi
  compact open immersion”. Eight hits include the quasi-affine class and the
  absolute canonical open immersion, but no relative chart-to-global result.
- Mathlib grep: `toSpecΓ|resLE|restrict.*[Cc]omp` in
  `AlgebraicGeometry/Restrict.lean`. Five hits locate restriction composition
  and `resLE`, which is used directly. Also read `QuasiAffine.lean`,
  `GammaSpecAdjunction.lean`, and the recorded dependency modules.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for
  `canonical.*[Aa]ffine.*[Cc]hart|affine.*[Cc]hart.*[Ii]mmersion|toSpecΓ`
  found many unrelated uses of canonical affinization, but no theorem for
  these hypotheses. Searching the item id in `lean/WeilConjectures` had no hit.
- Exact proposed name search `canonical_affine_charts|CanonicalAffineCharts`
  in Mathlib, WeilConjectures, Sheaf and `dag/lean_names_upstream.json`
  returned no hit before writing.

Validation: the prescribed server `scompile.py` compiled both the sandbox and
library view cleanly (6.5 s and 8.0 s). The dry-run validation is recorded below.

## Second reading by Q38

A second pass by the same worker reread the node and the module side by side;
this is not a claim of an independent second agent. The dispatcher explicitly
forbids starting another agent; independent maintainer review follows delivery.
The clause matching above was checked again, especially the composition order,
the inverse-image domains, and the compact convention for quasi-affineness.
`hc` produces exactly the containment argument of `resLE`; `hcharts` asserts an
isomorphism and the required canonical-map equality, rather than an arbitrary
map. The conjunction contains both requested conclusions and no extra one.
The universe is explicitly bound and arbitrary. The statement has no hidden
`let`, local notation, private data, or automatic implicit variables.
No mathematical mismatch was found. Direct imports of Scheme and OpenImmersion
were added to make the recorded statement-dependency imports explicit.

Delivery dry run: `deliver2.py Q38
lem-trf-canonical-affine-charts-qc-open-immersion --no-push` returned
`OK (dry run): commit 0e18719fc36 passes the preflight and compiles; nothing pushed`.
This includes clean recompilation after the two explicit dependency imports
were added. A final source check confirmed that only `lean` changed in the
node, the recorded signature is verbatim, the module has one `sorry`, and its
maximum line width is 85 characters.
