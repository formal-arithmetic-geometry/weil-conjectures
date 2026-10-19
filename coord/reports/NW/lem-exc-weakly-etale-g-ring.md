## Worker report

The new module `Sheaf.RingTheory.GRingOfWeaklyEtale` states
`RingHom.isGRing_of_weaklyEtale`, with one `sorry` and no definitions or proofs.
The node's mathematical statement is unchanged. Its only changed field is `lean`.
The docstring contains the ten complete natural-language proof steps from the DAG,
including the completed-local-map construction and the finite-product formal-fibre
calculation. All recorded proof-dependency modules are imported without `public`;
statement dependencies are public imports.

### Hypotheses and conclusion

| Node text | Lean rendering |
| --- | --- |
| A and B are commutative rings | `{A : Type u} {B : Type v} [CommRing A] [CommRing B]` |
| A and B are Noetherian | `[IsNoetherianRing A] [IsNoetherianRing B]` |
| A ring homomorphism f : A → B | `(f : A →+* B)` |
| f is weakly etale | `(hf : f.WeaklyEtale)` |
| A is a G-ring | `(hA : IsGRing A)` |
| B is a G-ring | conclusion `IsGRing B` |

`RingHom.WeaklyEtale f` installs precisely `f.toAlgebra` and asks for the
recorded `Algebra.WeaklyEtale A B`. This is not an independently supplied algebra
structure. Mathlib's class has the two exact flatness fields: `Module.Flat A B`
and `(Algebra.TensorProduct.lmul' A (S := B)).Flat`.
The root `IsGRing` definition includes Noetherianity and regularity of the
canonical maximal-ideal-adic completion map of every prime localization.
Both explicit Noetherian assumptions are retained as in the node (even though
Noetherianity of A is also a conjunct of `hA`). No finite presentation, finite
type, injectivity, faithful flatness, locality or residue-field finiteness is
assumed. Universes `u` and `v` are explicitly bound and independent.

### Dependency declarations read and used

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`; read its docstring and signature, and
  `isNoetherianRing_iff_ideal_fg`, confirming all ideals are finitely generated.
- `def-weil-pbc-ind-etale-algebra`: public import
  `Sheaf.RingTheory.IndPrincipalZariski`, whose recorded existing weak-etale
  clause is `Algebra.WeaklyEtale`, defined in `Mathlib.RingTheory.Etale.Weakly`.
  Read the full class and its flatness fields. The module also exposes
  `Algebra.IndEtale` and the scheme comparison declarations; these are not
  substituted for weak etaleness. Also public import
  `WeilConjectures.RingTheory.ProEtale.WeaklyEtale` for its existing ring-map
  wrapper `RingHom.WeaklyEtale`. Read both the local source and the current
  server source obtained by `scompile.py --source` and confirmed the wrapper
  uses `f.toAlgebra` and the same recorded class.
- `def-weil-pbc-g-ring`: `Sheaf.RingTheory.GRing`, `IsGRing`, and the definitions
  it uses, `RingHom.IsRegular` and `Algebra.IsGeometricallyRegular`. Read the
  full module, including all three docstrings and signatures. The geometric
  regularity tests use extensions in `Type (max u v)`, so there is no independent
  small test-field universe that would make their quantification vacuous.

The following already stated project proof dependencies are ordinary imports;
no new interface or dependency statement was necessary:

- `lem-pc-affine-flat-module-localization-preserves-flatness`: `Sheaf.RingTheory.Flat.LocalizationPreservesFlatness`, `Module.Flat.localizedModule_of_algebra`.
- `lem-weil-pbc-fibre-ring-noetherian`: `Sheaf.RingTheory.FibreRingNoetherian`, `Ideal.isNoetherianRing_fiber`.
- `lem-weil-pbc-ind-etale-stability`: `Sheaf.RingTheory.IndEtaleStability`, `RingHom.indEtale_principalZariski_stability`.
- `lem-weil-pbc-weak-etale-field`: `Sheaf.RingTheory.WeaklyEtaleField`, `Algebra.weaklyEtale_field`.
- `lem-weil-pbc-henselization-finite-separable-fibres`: `Sheaf.RingTheory.FiniteSeparableFibersOfEtaleColimit`, `CommAlgCat.finite_separable_fibers_of_etale_colimit`.
- `def-weil-pbc-formally-smooth-adic`: `Sheaf.RingTheory.FormallySmoothAdic`, `Algebra.FormallySmoothAdic`.
- `lem-weil-pbc-flat-formally-smooth-closed-fibre-adic`: `Sheaf.RingTheory.FormallySmoothAdicOfFlatClosedFiber`, `RingHom.formallySmoothAdic_of_flat_closedFiber`.
- `lem-weil-pbc-fs-adic-complete-source-target`: `Sheaf.RingTheory.FormallySmoothAdicCompleteSourceTarget`, `Algebra.exists_formallySmoothAdic_completeSourceTarget`.
- `lem-weil-pbc-adic-completion-noetherian`: `Sheaf.RingTheory.AdicCompletionNoetherian`, `AdicCompletion.isNoetherianRing`.
- `lem-weil-pbc-formally-smooth-complete-local-regular`: `Sheaf.RingTheory.FormallySmoothCompleteLocalRegular`, `RingHom.isRegular_of_formallySmoothAdic`.
- `lem-weil-pbc-regular-composition`: `Sheaf.RingTheory.RegularComposition`, `RingHom.IsRegular.comp_of_fiber_noetherian`.
- `lem-weil-pbc-localization-of-regular-ring`: `Sheaf.RingTheory.LocalizationOfRegularRing`, `RingTheory.isRegularRing_of_localization`.
- `lem-weil-pbc-geometric-regularity-separable-extension`: `Sheaf.RingTheory.GeometricRegularitySeparableExtension`, `Algebra.isGeometricallyRegular_iff_of_isSeparable`.

The Mathlib proof leaves use the existing flat local-ring map, localization-flatness,
separable-extension lifting, completion, tensor base-change and faithfully-flatness
interfaces; their modules are also ordinary imports.

### Source and edge cases

Read Greco's source PDF (saved only in sandbox scratchpad), printed pp. 139–140
and 146–147: the Foreword imposes commutative Noetherian rings; Section 1.1
includes geometric regularity among P; Remark 5.2 equates AF with the two-flatness
criterion for Noetherian rings; Theorem 5.3(i) says P-rings ascend along AF maps.
With this P it is exactly the G-ring claim. Also checked Stacks Tag 07GH online
against the recorded `IsGRing` definition.

- Zero target ring is allowed: there are no primes, so the completion-map
  universal condition is vacuous, while Noetherianity is retained.
- Zero source ring is allowed: a unital homomorphism from it forces the target
  to be the zero ring, so no excluded special case arises.
- Identity maps and ring isomorphisms are allowed; the statement requires no
  nontrivial extension or properness assumption.
- Field extensions are not restricted to finite degree. Separability and
  algebraicity occur in the proof, not as extra hypotheses on f.
- Disconnected rings and empty fibres are included. The proof explicitly allows
  an empty finite product in a fibre; the closed fibre of the localized local map
  is nonzero for the stated local argument.
- There is no characteristic restriction, chosen prime, nonzero element or
  index-type restriction in the declaration.
- No hypothesis is a tautology or an automatically available structure: the
  Noetherian instances and weak-etale condition constrain the input rings/map;
  `IsGRing A` includes the substantive formal-fibre regularity assertion.

### Searches

- `msearch.py ... leanfinder "A weakly etale homomorphism of Noetherian rings
  preserves the G ring property"`: eight hits, on etale algebra maps, finite
  presentation/descent and composition/locality; none states G-ring ascent.
- `msearch.py ... loogle "IsGRing, WeaklyEtale"`: zero hits; the Mathlib search
  reports unknown identifier `IsGRing`.
- `msearch.py ... grep "IsGRing|G-ring|geometrically.?regular" RingTheory`:
  zero Mathlib hits.
- `msearch.py ... leansearch "Weakly etale homomorphisms of Noetherian rings
  preserve G rings"`: eight etale/formally-etale composition and base-change
  hits, none about G-rings.
- `rg -n` in the upstream `WeilConjectures/` for the item id, `IsGRing`, and
  `isGRing_of_weaklyEtale`: no existing theorem or G-ring definition there.
- `rg -n` in `lean/Sheaf`, `dag/nodes` and `dag/lean_names_upstream.json`
  for `IsGRing`, `WeaklyEtale` and `isGRing_of_weaklyEtale`: reused the recorded
  definitions; found finite-type, completion, quotient, ring-equivalence and
  henselization G-ring lemmas, but none is the arbitrary weakly-etale ascent
  statement. `ExcellentOfWeaklyEtale` cites this item in its proof plan and is a
  consumer, not a duplicate. No declaration with the chosen full name exists.

No new nodes, dependency repairs, statement correction or statement dispute.

### Validation

`scompile.py NW lem-exc-weakly-etale-g-ring
lean/Sheaf/RingTheory/GRingOfWeaklyEtale.lean` passed with no errors or warnings:
the sandbox check took 31.7 s and the library-module check took 51.7 s, each
within the 60-second per-file limit. `set_option autoImplicit false` and explicit
`universe u v` enforce the binding convention. The sole theorem proof is `sorry`.
The node signature was extracted from the exact theorem text and JSON uses
indentation 1, Unicode and a final newline.

Required delivery validation: `deliver2.py NW lem-exc-weakly-etale-g-ring --no-push`.
The independent second reader writes the second-reading section and delivers;
this worker only runs the dry run.

## Second reading by NW

Independent reading of the node, its three statement-dependency records and their
actual declarations, the sandbox module, and Greco's source (sandbox
`scratchpad/greco.txt`, printed pp. 139–140 and 146–147). No mathematical or Lean
mismatch found; the statement, imports, docstrings and node record need no repair.
This second reading adds only this review to the report.

The source's Foreword assumes all rings commutative and Noetherian. Section 1.1
allows P = geometrically regular and defines P-rings using formal fibres at prime
(or maximal) ideals. Remark 5.2 identifies AF, for these Noetherian rings, with
flatness over A and over B tensor_A B. Theorem 5.3(i) asserts ascent of P-rings
along AF maps; faithful flatness appears only for its converse in (v). Thus the
node correctly specializes (i) to G-rings without adding faithful flatness or
finite presentation. I also opened Stacks [07GH](https://stacks.math.columbia.edu/tag/07GH),
[07BZ](https://stacks.math.columbia.edu/tag/07BZ) and
[0381](https://stacks.math.columbia.edu/tag/0381): these give the prime-local
completion definition, regular-map definition and finite purely inseparable
extension criterion used by the dependency. The local Stacks tex files are not
present in this checkout, so these primary-source pages supply that check.

The complete list of objects, hypotheses and conclusion, matched independently:

| Node clause | Actual Lean rendering | Verdict |
| --- | --- | --- |
| A is a commutative ring | `{A : Type u} [CommRing A]` | Exact; unital commutative ring, including the zero ring. |
| B is a commutative ring | `{B : Type v} [CommRing B]` | Exact; no field or domain assumption. |
| A is Noetherian | `[IsNoetherianRing A]` | Exact; Mathlib `IsNoetherianRing` and `isNoetherianRing_iff_ideal_fg` say every ideal is finitely generated. |
| B is Noetherian | `[IsNoetherianRing B]` | Exact; explicitly retained as in Greco and the node. |
| A specified homomorphism f : A → B | `(f : A →+* B)` | Exact; neither locality nor injectivity is assumed. |
| f is weakly etale | `(hf : f.WeaklyEtale)` | Exact; the upstream wrapper uses `f.toAlgebra`, then the recorded Mathlib `Algebra.WeaklyEtale`. |
| A is a G-ring | `(hA : IsGRing A)` | Exact; uses the dependency's prime-local completion definition. |
| B is a G-ring | `: IsGRing B` | Exact; all primes of B are quantified inside the definition, with no chosen-prime restriction. |

Opened `Sheaf.RingTheory.IndPrincipalZariski` and the dependency node: its
weak-etale clause explicitly reuses `Algebra.WeaklyEtale`. Opened the upstream
`WeilConjectures.RingTheory.ProEtale.WeaklyEtale` wrapper and Mathlib
`RingTheory/Etale/Weakly.lean`: the two class fields are `Module.Flat A B` and
flatness of `Algebra.TensorProduct.lmul' A (S := B)`. An unrelated externally
chosen algebra structure cannot enter the hypothesis. The principal ind-Zariski
notion defined elsewhere in that dependency module is not used instead.

Opened all of `Sheaf.RingTheory.GRing`, including the signatures and bodies of
`Algebra.IsGeometricallyRegular`, `RingHom.IsRegular` and `IsGRing`. These use
Noetherianity, geometric regularity of every prime fibre, and the canonical
maximal-ideal-adic completion of `Localization.AtPrime p`, respectively.
Mathlib `IsRegularRing` requires Noetherianity and regularity of every prime
localization. The finite purely inseparable test fields live in
`Type (max u v)`, which admits the identity extension and representatives of
all finite extensions; this is not a vacuous small-universe test. The order of
quantification in the theorem is precisely rings, map, weak etaleness, source
G-ring, then target G-ring. No extra instances occur.

Edge cases checked: either ring may be zero; a homomorphism from the zero ring
forces the target zero, and the prime condition for a zero target is vacuous.
Identity maps, ring isomorphisms, disconnected rings, and nonfaithful maps to the
zero ring are admitted. Empty fibres and the empty finite product in proof step
3 are admitted; the local closed fibre in step 4 is nonzero for the stated
reason. No index set or natural-number parameter occurs in the signature, so
there is no hidden nonemptiness or positive-degree assumption. The proof's
completion coordinates include n = 0. No characteristic or finiteness of
residue-field degree is assumed. Explicit `universe u v` allows independently
sized rings, and `set_option autoImplicit false` leaves no unbound variables.

Independent searches used different terms from the first reader:

- LeanFinder via `msearch.py`: "regularity of formal fibres ascends through
  absolutely flat homomorphisms between noetherian rings". Eight hits, chiefly
  regular-sequence ascent and flatness; none states this theorem.
- Loogle via `msearch.py`: `RingHom.WeaklyEtale, IsGRing`. No hits; its Mathlib
  index does not know the project's/upstream wrapper identifier.
- LeanSearch via `msearch.py`: "A ring with geometrically regular formal fibers
  remains a G ring after an absolutely flat noetherian extension". Eight hits
  on regular sequences, geometric reducedness and formal smoothness; no match.
- Grep via `msearch.py`: `G-ring|IsGRing|formal fib[er]` in RingTheory. No hits.
  Direct `rg` searches for `IsGRing`, `G-ring`, `geometrically.?regular` and
  `formal fib[er]` in Mathlib RingTheory, upstream `WeilConjectures/` and
  `lean/Sheaf/RingTheory/` find only project special cases and definitions.
  More specifically, finite-type ascent requires `Algebra.FiniteType`,
  henselization ascent concerns a particular henselization, completion
  regularity concludes regularity of a completion map, and ring-equivalence
  transport requires an equivalence. None covers arbitrary weakly etale maps.
  The exact theorem name and item id have no duplicate declaration in upstream,
  the upstream name registry or `lean/Sheaf/`; `ExcellentOfWeaklyEtale` is a
  consumer with this item in its proof plan.

H5–H9 check: the delivered module has no definitions, one theorem with `sorry`,
and no proved lemmas, private constructions, file-local notation or instances.
The source/blueprint docstrings are present. I read all ten proof paragraphs:
localization; the localized multiplication criterion; finite-product separable
fibres; formally smooth closed fibre; the compatible completion map; complete
local regularity; regular composition; tensor-product factorization;
localization of geometric regularity; and separable-extension descent of each
formal fibre. They carry the node's proof and its named dependencies. Every
recorded proof-dependency module or Mathlib leaf module is imported without
`public`; statement dependencies are public imports. All lines have at most
100 characters. Mechanical comparison confirms that the node's `lean.statement`
is verbatim the theorem signature, and `lean` is the only changed node field.
There are no new nodes, dependency modules, statement corrections or unresolved
disputes to audit.

Second-reader validation: reran the required `scompile.py NW
lem-exc-weakly-etale-g-ring lean/Sheaf/RingTheory/GRingOfWeaklyEtale.lean` from
the sandbox. Both sandbox and library-path checks passed, exit 0, with no
errors or warnings. The reported elapsed times were 50.6 s and 253.9 s;
the latter includes shared-slot queueing before the unchanged 60 s compiler
limit begins. A separate whitespace-normalized comparison confirms all ten
proof paragraphs reproduce their corresponding DAG proof steps exactly.
