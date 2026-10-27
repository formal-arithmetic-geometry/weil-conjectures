# finiteGlobalDirectPowerTransport

## Reason

The item duplicated `compactDirectPowerTransport`, already constructed in
`Sheaf.TraceFormula.CompactDirectPowerTransportNormalization`. Both are direct
power-square exchanges retaining the same compactification; neither is constructed
by repeating degree-one transport. Merge the duplicate into an abbreviation of that
canonical construction, as required by stages/3-proving-and-pruning.md §3. The old
construction's large proof-valued Cartesian witnesses and dependent pullback aliases
made comparisons repeatedly unfold the derived category's Shrink models and exceed
the time limit. Sharing the existing direct construction removes this cost.

This is a definition repair, not a change to the theorem statement or a replacement
of a direct construction by the repeated transport it must be proved to equal. The
actual equality with repeated transport remains the separate imported theorem
`compact_direct_power_transport_normalization`, still a proof task of its own.

Semantic check: expand compactPowerTransport and compactPowerExchange. Their first
factor is the same pointPowerTransportFinite. The finiteCompact square arguments
agree; their proof witnesses agree by proof irrelevance. The point model comparison
is the inverse of openSquareDerivedPullbackModel: compose the defining unit equations
of integralFinitePullbackModel and openSquarePullbackModel, then use uniqueness of the
intrinsic inverse-image left adjoint and exact derived descent. Consequently the
additional fibre pullback-model factor in compactPowerTransport cancels its inverse
in compactDirectPowerTransport, leaving exactly the old formula. This calculation
also applies at level one, exponent one, and the zero object; level zero is excluded
by the existing positivity hypothesis. No new hypothesis or equality convention is
introduced. The named public theorem retains its exact original signature.

The module newly publicly imports CompactDirectPowerTransportNormalization, since
the abbreviation uses its definition. Both original public imports are retained.
Only local elaboration settings are otherwise changed: transparency is respected,
and large functors/transport interfaces are locally irreducible in the proof.

## Old

```lean
def finiteGlobalDirectPowerTransport (T : TraceFormulaCoefficientConventions.{u})
    (c₀ : Compactification T.X₀.hom)
    (M : proEtaleDerivedCategory T.geometricBaseChange T.coefficientRing) (r : ℕ) :
    (T.finiteGlobalCompactSections c₀).obj M ⟶
      (T.finiteGlobalCompactSections c₀).obj ((T.frobeniusPullbackPower r).obj M) := by
  rcases T with ⟨D, C, E, n, hn, X, hft, hqc, hsep⟩
  cases n with
  | zero => omega
  | succ n =>
    let F := AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E
    let A := Padic.coefficientExtensionRing C.l F (n + 1)
    letI : Finite A := Padic.finite_coefficientExtensionRing C.l F (n + 1) hn
    let c := frobeniusCohomologyCompactification D X c₀
    let gX : End (D.geometricFiber X).left := galois D X
    let gB : End c.Z :=
      galois D (zlCompactificationMiddle D (frobeniusCohomologyModelMap D X) c₀)
    let h := pointFrobeniusAut D
    have sp₁ : IsPullback gB c.g c.g h.hom :=
      (D.frobenius_square_cartesian
        (zlCompactificationMiddle D (frobeniusCohomologyModelMap D X) c₀)
        (sfWeilCohomologyPoint D)
        (zlCompactificationProper D (frobeniusCohomologyModelMap D X) c₀)).the project server.2.2.2
    have sj₁ : IsPullback gX c.i c.i gB :=
      (D.frobenius_square_cartesian X
        (zlCompactificationMiddle D (frobeniusCohomologyModelMap D X) c₀)
        (zlCompactificationOpen D (frobeniusCohomologyModelMap D X) c₀)).the project server.2.1
    have sp : ∀ m : ℕ, IsPullback (gB ^ m) c.g c.g (h ^ m).hom := by
      intro m
      induction m with
      | zero => exact IsPullback.id_horiz _
      | succ m ih =>
        simpa only [pow_succ, End.mul_def, Aut.Aut_mul_def, Iso.trans_hom] using
          sp₁.paste_horiz ih
    have sj : ∀ m : ℕ, IsPullback (gX ^ m) c.i c.i (gB ^ m) := by
      intro m
      induction m with
      | zero => exact IsPullback.id_horiz _
      | succ m ih =>
        simpa only [pow_succ, End.mul_def] using sj₁.paste_horiz ih
    let H := sfIntrinsicCompactSupport c A
    let e := finiteCompact C.l F (n + 1) hn c (gX ^ (r + 1)) (gB ^ (r + 1))
      (h ^ (r + 1)).hom (sp (r + 1)).w (sj (r + 1))
    exact pointPowerTransportFinite D C.l C.different F (r + 1) n (H.obj M) ≫
      (finiteLocalSections ⟨D, C, E, n + 1, hn, X⟩).map
        ((pointPowerPullbackModel C.l F n (h ^ (r + 1)).hom).hom.app (H.obj M) ≫
          e.app M)
```

## New

```lean
abbrev finiteGlobalDirectPowerTransport (T : TraceFormulaCoefficientConventions.{u})
    (c₀ : Compactification T.X₀.hom)
    (M : proEtaleDerivedCategory T.geometricBaseChange T.coefficientRing) (r : ℕ) :
    (T.finiteGlobalCompactSections c₀).obj M ⟶
      (T.finiteGlobalCompactSections c₀).obj ((T.frobeniusPullbackPower r).obj M) :=
  T.compactDirectPowerTransport c₀ M r
```

## Users

Both `python3 tools/downstream.py Sheaf.Paper.FrobeniusOperatorCompactDescription
--uses finiteGlobalDirectPowerTransport` and the analogous query for
`frobenius_operator_compact_description` report zero downstream modules and only the
item itself as a name user. No existing consumer requires adaptation. No target
statement in Challenge.lean uses this declaration. The DAG statement still describes
the same canonical direct base-change map and retains its Lean attachment.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.FrobeniusOperatorCompactDescription | B4 | Duplicate definition merged; theorem proved. |

## Status

landed 20261025T201411-L-2482608 2026-10-25 (merge of deliver/B4/Sheaf.Paper.FrobeniusOperatorCompactDescription)
