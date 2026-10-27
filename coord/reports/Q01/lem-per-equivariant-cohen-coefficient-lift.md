## Worker report

The module `Sheaf.RingTheory.EquivariantCohenCoefficientLift` states
`IsLocalRing.exists_equivariant_cohen_coefficient_lift`, with one `sorry` and no new
definitions. The node's statement, dependencies, and proof are unchanged. The source
is ILO, Travaux de Gabber, Exposé IV 4.3.5–4.3.6, printed p.60, read directly in
the local PDF (PDF p.66), with the coefficient construction of 4.1 and 4.2.5.
No repair note exists for the item. The original example CompactObject module
is now withdrawn; its node and the current module-mode convention were read.

Hypotheses, clause by clause:

- `W : Type u`, `[CommRing W]`, `[IsDomain W]`, `[IsDiscreteValuationRing W]`
  give the DVR. `[IsAdicComplete (maximalIdeal W) W]` gives its completeness.
- `[CharZero W]`, `p : ℕ`, `hp : Nat.Prime p`, and
  `[CharP (ResidueField W) p]` give mixed characteristic `(0,p)`.
- `π : W`, `hπ : Irreducible π` give the uniformizer, using Mathlib's
  `IsDiscreteValuationRing.irreducible_iff_uniformizer`. Thus `ResidueField W`
  is exactly the node's `k0 = W/(π)`, canonically identified using this equality
  of ideals. `hperfect` is literally bijectivity of `x ↦ x ^ p` on this field.
- `C : Type v`, its commutative-ring, local-ring, Noetherian-ring and
  maximal-ideal-adic completeness instances give `(C,n)` as stated.
  `[Algebra W C]` and `[IsLocalHom (algebraMap W C)]` give its local structure
  map. `ResidueField C` is precisely `k' = C/n`.
- `H : Type w`, `[Group H]`, `[Finite H]` give an arbitrary finite group.
  `horder : IsUnit (Nat.card H : W)` expresses invertible order without
  assuming commutativity or choosing an enumeration.
- `ρW : H →* RingAut W` and `ρC : H →* RingAut C` are the two actions by
  ring automorphisms. Ring automorphisms of local rings are automatically local.
  `hcompat` states compatibility with the structure map for every `h` and `a`.
  The residue action is the canonical `ResidueField.mapAut (ρC h)`.
- `s : ResidueField C →ₐ[W] C ⧸ Ideal.span {algebraMap W C π}` is the section
  into `C/πC`. This is exactly a `k0`-algebra map: both W-actions factor
  canonically through the surjection `W → k0`; W-linearity and k0-linearity
  are equivalent. No choice of coefficient field is required or assumed.
- `hsection` says the canonical quotient map `C/(π) → C/n`, composed with
  `s`, is the identity. `Ideal.Quotient.factor` constructs this map. Its
  containment proof is the existing theorem `map_nonunit` applied to the
  local structure map and the fact that a uniformizer is not a unit.
- `hsequiv` gives equivariance on every representative `c` of `s x`: applying
  `ρC h` takes it to a representative of `s (h x)`. The ideal `(πC)` is stable
  because `ρW h` preserves the maximal ideal `(πW)` and the structure map is
  equivariant. Every quotient element has a representative, so this is exactly
  equivariance of `s` for the induced quotient action, not an extra assumption.

Conclusion, clause by clause:

- Existential `V : Type (max u v)` and its ring/domain/DVR instances give the
  coefficient DVR. The tensor construction fits in this universe without any
  equality between the input universes; the group universe is independent.
- The existential `Algebra W V` supplies its structure map.
  `IsAdicComplete (maximalIdeal V) V` gives completeness,
  `IsLocalHom (algebraMap W V)` gives localness, and
  `Function.Injective (algebraMap W V)` gives injectivity. Its characteristic
  is therefore zero, inherited through this injection from W.
- `maximalIdeal V = Ideal.span {algebraMap W V π}` says π is a uniformizer.
  `e : (V ⧸ Ideal.span {algebraMap W V π}) ≃ₐ[W] ResidueField C`
  supplies the specified residue-field identification, compatible with W.
- `Algebra.FormallySmoothAdic W V (maximalIdeal V)` uses the recorded
  adic notion, not ordinary algebraic formal smoothness.
- `ρV : H →* RingAut V` supplies the action. Its first equation intertwines
  the structure map with `ρW`; its second equation says `e` transports the
  induced quotient action to the given action on `k'`.
- `ψ : V →ₐ[W] C` and `IsLocalHom ψ.toRingHom` give the local W-algebra map.
  The next equation is H-equivariance. The final equation is exactly
  `q_C(ψ(a)) = s(e(q_V(a)))`, fixing the full reduction modulo π.
  There is no injectivity claim on ψ and no injection of W into C assumed.

Dependency declarations read and used:

- `Mathlib.RingTheory.DiscreteValuationRing.Basic`:
  `IsDiscreteValuationRing`, `IsDiscreteValuationRing.irreducible_iff_uniformizer`.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `IsAdicComplete`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `WeilConjectures.RingTheory.FormallySmoothAdic`: `Algebra.FormallySmoothAdic`.
  Its test rings have universe `max u v`, retained without specialization.
- Canonical maps and actions from
  `Mathlib.RingTheory.LocalRing.ResidueField.Basic`:
  `IsLocalRing.ResidueField`, `IsLocalRing.residue`,
  `IsLocalRing.ResidueField.mapAut`; and `Ideal.Quotient.factor` from
  `Mathlib.RingTheory.Ideal.Quotient.Defs`, already publicly available.

Proof dependencies already recorded/imported are `IsGalois.of_fixed_field`
(`Mathlib.FieldTheory.Galois.Basic`), the tensor product API
(`Mathlib.RingTheory.TensorProduct.Maps`), `exists_cohenRing`
(`WeilConjectures.RingTheory.CohenRingsExist`),
`RingHom.exists_lift_of_field_charP`
(`WeilConjectures.RingTheory.ExistsLiftOfFieldCharP`),
`RingHom.formallySmoothAdic_of_flat_closedFiber`
(`WeilConjectures.RingTheory.FormallySmoothAdicOfFlatClosedFiber`), and
`quotient_complete_local` (`WeilConjectures.RingTheory.CompleteLocalQuotient`).
The three proof-only nodes `lem-per-finite-etale-cohen-extension`,
`lem-per-perfect-cohen-residue-map`, and `lem-per-ramified-cohen-tensor-dvr`
have no recorded declarations yet, so their imports cannot be supplied now;
they are retained in the node's unchanged proof dependencies and named in the
eight-step proof docstring. All statement dependencies are usable as recorded.
No dependency modules or new nodes are needed.

Edge cases checked before writing:

- Trivial H and nonfaithful actions are included; no faithfulness hypothesis.
- Nontrivial semilinear action on W is included; π need not be pointwise fixed.
- C may be a residue field with π mapping to zero: ψ can then have nonzero
  kernel. The quotient is C itself and no injectivity assumption excludes it.
- Nilpotents in C and arbitrary ramification of W are allowed.
- k' need not be perfect, finite, algebraic, or finitely generated over k0.
- p=2 is allowed; the excluded characteristic-zero residue field is excluded
  exactly by the source's mixed-characteristic hypothesis.
- The zero ring cannot be a local ring under this Mathlib convention, as required
  by having a residue field. A finite group is nonempty automatically.

Searches performed using the prescribed `msearch.py` (all succeeded; records are
in sandbox `searches.jsonl`):

- LeanSearch: `Equivariant Cohen coefficient extension of a complete discrete
  valuation ring and lifting a residue field section`. Eight hits including
  `Ideal.ResidueField.liftₐ`, `Ideal.ResidueField.lift`, and
  `IsLocalRing.ResidueField.lift_residue_apply`; none constructs the stated DVR.
- LeanFinder: `Equivariant formally smooth Cohen coefficient discrete valuation
  ring lifting section finite group`. Eight hits including
  `Algebra.FormallySmooth.exists_lift` and adic completion lifting; none provides
  the coefficient extension, semilinear action and fixed section simultaneously.
- Loogle: `IsDiscreteValuationRing, IsAdicComplete`. No hits.
- Mathlib grep: `Cohen|equivariant.*lift`, subdirectory `RingTheory`.
  Only a bibliographic reference to Cohen in `Noetherian/OfPrime.lean`.
- `rg -n -i 'equivariant.*cohen|cohen.*equivariant'` in the project's
  `lean/WeilConjectures` and `lean/Sheaf` found only the unrelated relative
  coordinate-lift module, whose full statement was read; it assumes a given
  Cohen power-series presentation and constructs new coordinates.
- `rg -n 'lem-per-equivariant-cohen-coefficient-lift' lean/WeilConjectures`
  returned no hits. The declaration-name/`equivariant_cohen` search in Mathlib,
  both source roots, and `dag/lean_names_upstream.json` returned no hits.

Validation: `scompile.py Q01 lem-per-equivariant-cohen-coefficient-lift ...`
compiled the sandbox and final module on the server cleanly (22.7 s and 1.4 s),
with no errors or warnings. Both auto-implicit options are explicitly false.
The JSON signature is extracted verbatim from the module. No statement dispute
or statement correction arose.


## Second reading by Q01

Independent second reading by the maintainer's reviewer (the delivered section was
the author's own self-audit). I read the node statement, ILO IV 4.3.5–4.3.6 (the
node's source place, with the 4.1.3–4.1.9 and 4.2.5 coefficient construction), all
four stmt_dep records, and `IsLocalRing.exists_equivariant_cohen_coefficient_lift`.

| Node clause | Lean | Verdict |
|---|---|---|
| W complete DVR (def-sc-discrete-valuation-ring, def-weil-pbc-adically-complete-ring) | `[IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]` | exact (recorded Mathlib owners) |
| mixed characteristic (0,p) | `[CharZero W]`, `hp : Nat.Prime p`, `[CharP (ResidueField W) p]` | exact |
| uniformizer π | `hπ : Irreducible π` (= uniformizer by `irreducible_iff_uniformizer`) | exact |
| k0 = W/πW perfect | `hperfect : Bijective (x ↦ x^p)` on `ResidueField W` (= W/(π) since (π) = m_W) | exact (node: "perfect means bijective Frobenius") |
| (C, n) complete Noetherian local W-algebra, local structure map (def-weil-pbc-noetherian-ring) | `[IsLocalRing C] [IsNoetherianRing C] [Algebra W C] [IsLocalHom (algebraMap W C)] [IsAdicComplete (maximalIdeal C) C]` | exact; no injectivity of W → C and no mixed characteristic on C |
| k' = C/n | `ResidueField C` | exact |
| finite group H, order invertible in W | `[Group H] [Finite H]`, `IsUnit (Nat.card H : W)` | exact |
| H acts by local ring automorphisms on W, C, compatibly | `ρW : H →* RingAut W`, `ρC : H →* RingAut C`, `hcompat` | exact (ring automorphisms of local rings are local; no faithfulness and no fixing of π) |
| induced actions on k0, k' | `ResidueField.mapAut (ρC h)` | canonical Mathlib map |
| H-equivariant k0-algebra section s : k' → C/πC | `s : ResidueField C →ₐ[W] C ⧸ (π)` (W-linear ⇔ k0-linear as W ↠ k0 acts through both) with `hsection` (`Ideal.Quotient.factor` composite = id) and `hsequiv` (on all representatives c ⇔ quotient equivariance; πC is H-stable by `hcompat`) | exact |
| ∃ complete DVR V, W → V local injective | `∃ V : Type (max u v)`, DVR instances, `Algebra W V`, `IsAdicComplete`, `IsLocalHom`, `Injective` | exact; the universe covers W ⊗_A B with no input-universe equality |
| V/πV ≅ k', π uniformizer of V | `maximalIdeal V = span {π}`, `e : V ⧸ (π) ≃ₐ[W] ResidueField C` | exact (W-algebra iso records the residue inclusion k0 → k') |
| H-action on V compatible with W and k' | `ρV`, the structure-map clause, and the `e`-transport clause | exact |
| W → V formally smooth for the m_V-adic topology (def-weil-pbc-formally-smooth-adic, Stacks 07NI) | `Algebra.FormallySmoothAdic W V (maximalIdeal V)` | exact (recorded upstream def, test rings `Type (max u v)`) |
| H-equivariant local W-algebra map ψ : V → C with reduction s ∘ (V → k') | `ψ : V →ₐ[W] C`, `IsLocalHom ψ.toRingHom`, the equivariance clause, `q_C ∘ ψ = s ∘ e ∘ q_V` | exact; no injectivity of ψ |

Edge cases: H trivial or acting non-faithfully; semilinear action on W; C = k' with
π ↦ 0 (ψ then has a kernel and the statement stays true: V → k' works); non-perfect,
non-algebraic k'/k0; p = 2. A characteristic-0 residue field is excluded, as in the
source. The quantifier order is the node's, with all existentials together.

Searches: Mathlib has no Cohen-ring or adic formal-smoothness API
(`rg -i "cohen|FormallySmoothAdic"` in RingTheory finds only a bibliographic
reference). In the project tree, `exists_equivariant_cohen_coefficient_lift` and the
module path are absent from side-live, so there is no name clash. One definition per
notion holds: all notions are recorded stmt_dep owners or canonical Mathlib maps.

Records: the node differs from live only in its new `lean` field. `lean.statement`
occurs verbatim in the file, once. Docstrings carry the source place,
`(blueprint: lem-per-equivariant-cohen-coefficient-lift)` and the eight proof steps.
There is one `sorry` and no new definitions. The item is on route-pivot-dropped.txt
(l.1510), but it is reached through the non-dropped lem-per-complete-local-nodal-
dimension-reduction (via marked-algebraization and equivariant-cohen-presentation),
so the delivery stands. No mismatch was found; nothing was changed in the Lean.
