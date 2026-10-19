## Worker report

The delivery states `AlgebraicGeometry.exists_projective_localization_of_completeDevissage`
in `Sheaf.TraceFormula.CompleteDevissageProjectiveLocalization`. Its sole theorem has
proof `sorry`; no new definition or additional node is needed. The item's node copy
changes only `lean`. I read the node, all six statement dependencies and their binding
records, the recorded declaration sources and docstrings, and Stacks flat.tex,
Definition 05HX, Remark 05HY, and Lemma 05IB with its proof.

The node selects the projectivity conclusion of 05IB. The source also gives a direct-sum
decomposition, which this node does not assert. The nine-step proof plan in the module
follows the node's induction, finite-presentation transfers, generic-basis shrinking,
localization, flat cokernel, induction on the tail, projectivity of the smooth algebras,
splitting, and combination of two localizations.

Hypothesis and clause correspondence:

| Node | Lean |
| --- | --- |
| Commutative rings and a homomorphism R to S | `(R S : Type u) [CommRing R] [CommRing S] [Algebra R S]`; the map is `algebraMap R S`. |
| R to S of finite presentation | `[Algebra.FinitePresentation R S]`. |
| An S-module N | `(N : Type v) [AddCommGroup N] [Module S N]`. |
| N as an R-module via the given homomorphism | `[Module R N] [IsScalarTower R S N]`; this says exactly that the R-action is the restricted S-action. These are compatible scalar structures, not an extra flatness or finiteness condition. |
| N finitely presented over S | `[Module.FinitePresentation S N]`; Mathlib derives `Module.Finite S N` for the devissage structure. |
| N flat over R | `[Module.Flat R N]`, using the dependency's module notion, not flatness of S. |
| A prime ideal r of R | `(r : Ideal R) [r.IsPrime]`. |
| N/S/R admits a complete devissage over r | `hdev : Nonempty (CompleteAlgebraDevissage R S r N)`, the exact recorded definition, including all finite maps, cokernels and generic-fibre bases. Algebra finite type is inferred from finite presentation. |
| There exists f in R outside r | `∃ f : R, f ∉ r ∧ ...`. |
| R_f inverts the powers of f | `Localization.Away f`, Mathlib's localization at `Submonoid.powers f`. |
| N_f is the module of fractions m/f^k, equivalently N tensor_R R_f | `LocalizedModule (Submonoid.powers f) N`; this is the canonical fraction construction, not an arbitrary localized module. |
| N_f is projective over R_f | `Module.Projective (Localization.Away f) (LocalizedModule (Submonoid.powers f) N)`. |
| No finite generation or finite presentation over R assumed | Neither `Module.Finite R N` nor `Module.FinitePresentation R N` occurs. |

Dependency declarations used:

- `def-weil-pbc-finitely-presented-algebra`: `Algebra.FinitePresentation`,
  `Mathlib.RingTheory.FinitePresentation`; read the class with its polynomial presentation.
- `def-sc-finitely-presented-module`: `Module.FinitePresentation`,
  `Mathlib.Algebra.Module.FinitePresentation`; read its finite generating set and
  finitely generated relation kernel, and its finite-module instance.
- `def-weil-pbc-flat-ring-map`: `Module.Flat`, `Mathlib.RingTheory.Flat.Basic`,
  publicly available through the recorded `Mathlib.RingTheory.RingHom.Flat`.
  The injective-tensor criterion matches the node; `RingHom.Flat` itself is not
  imposed on R to S.
- `def-trf-complete-algebra-devissage`: `AlgebraicGeometry.CompleteAlgebraDevissage`,
  `Sheaf.TraceFormula.CompleteAlgebraDevissage`; read the whole structure, including
  its zero-length case, module universe, scalar restriction and residue-field maps.
- `def-weil-pbc-projective-module`: `Module.Projective`,
  `Mathlib.Algebra.Module.Projective`; read the split canonical free-module surjection
  and the lifting-property theorem.
- `def-weil-pbc-module-tensor-product`: `TensorProduct`,
  `Mathlib.LinearAlgebra.TensorProduct.Defs` via `Mathlib.LinearAlgebra.TensorProduct.Basic`.
  The conclusion uses the node's explicitly permitted equivalent fraction-module form.

All available recorded proof-dependency modules are imported, including
`Sheaf.RingTheory.FiniteExtensionModuleFinitePresentation`,
`Sheaf.RingTheory.AffineGeometricallyIntegralProjective`,
`Sheaf.TraceFormula.LocalUIFlatCokernel`, the upstream
`WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced`, and the corresponding
Mathlib modules for smoothness, integrality, base change, finite presentation and
localization. `lem-trf-generic-basis-base-open-universal-injectivity` has no recorded
Lean statement in the read snapshot, so there is no module of that proof dependency
to import. It is named explicitly in step 4 of the proof plan. No missing statement
notion is replaced by a private copy.

Edge cases checked:

- For N = 0 a complete devissage may have length zero and the conclusion holds with
  f = 1 and the zero localized module. `Nonempty` does not force positive length.
- Length one and rank zero are allowed by the imported structure. The induction plan
  handles the zero cokernel and the zero free summand explicitly.
- No nonzero-ring assumption is imposed. The prime-ideal binder already excludes a
  prime in a zero ring; zero S and zero N remain allowed over a base with a prime.
- The unit f = 1 remains allowed; no nonunit or nonzero-prime restriction is introduced.
- R = k, S = k[x], N = S illustrates why no finite-R-module hypothesis may be added:
  this smooth geometrically integral example is covered although N is infinite
  dimensional over k.
- R and S share the ring universe used by the recorded devissage definition; u is
  arbitrary, and the independent v for N is retained. No equality with the module
  universe or any testing-algebra universe is assumed.

Searches made using the prescribed wrapper, with exact records in `searches.jsonl`:

- LeanFinder: "A flat finitely presented module over a finitely presented algebra with
  complete devissage is projective after localization outside a base prime".
  Eight hits, including `Module.Flat.projective_of_finitePresentation`,
  `Module.projective_of_localization_maximal`, `Module.basicOpen_subset_freeLocus_iff`
  and `Module.FinitePresentation.exists_notMem_bijective`; none gives this statement.
- Loogle: `Module.Projective, Localization.Away`. One hit,
  `Module.basicOpen_subset_freeLocus_iff`, requiring finite presentation over R.
- Mathlib grep: `devissage|Devissage|projective_of_finitePresentation`.
  Three hits in Flat/EquationalCriterion and Etale/Descent; no devissage notion.
- LeanSearch: "A module flat over R finitely presented over a finitely presented R
  algebra with a complete devissage becomes projective on a principal base open
  neighborhood". Its result is recorded in the search log; the returned general
  flatness/projectivity criteria do not provide complete devissage over an algebra.
- Direct `rg` for `CompleteAlgebraDevissage|complete.*devissage|devissage.*projective`
  in upstream WeilConjectures and side `lean/Sheaf`: the imported definition and the
  parent theorem's docstring; no matching theorem.
- Direct `grep -rn` for this item's id in upstream WeilConjectures: no hits.
- Direct `rg` for the new theorem name in Mathlib, upstream WeilConjectures,
  side `lean/Sheaf`, and `dag/lean_names_upstream.json`: no hits.

I opened the actual Mathlib signatures of the closest candidates:
`Module.Flat.projective_of_finitePresentation` assumes finite presentation as an
R-module, as does `Module.basicOpen_subset_freeLocus_iff`. They cannot replace the
node. No statement correction, disputed statement, new node or dependency repair
is needed.

Validation: `scompile.py Q155 lem-trf-complete-algebra-devissage-projective-localization`
compiled the delivered statement as both sandbox and library module without errors
or warnings (2.7 s and 2.8 s for the first pass). The delivery wrapper repeats compilation
and runs the server preflight before pushing.

## Second reading by Q155

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
