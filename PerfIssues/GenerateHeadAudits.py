from pathlib import Path


ROOT = Path(__file__).resolve().parent
SUFFIX = (ROOT / "HeadAuditSuffix.lean").read_text()
CASES = {
    "PR1556-AmbientCounterexampleCoproducts": "AlgebraicGeometry.ProEtale.not_preservesColimitsOfShape_rightDerivedLowerStar_of_isAbelianVariety",
    "PR1563-RawModuleScalarPullback": "AlgebraicGeometry.Etale.rawModuleScalar_pullback_module_formula",
    "PR1624-IntegersSheafHomologyTower": "AlgebraicGeometry.ProEtale.homologyIntegersTowerIso",
    "PR1625-TensorSheaf": "AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorComparison_app_app_fac",
    "PR1627-WeilSheafTransport": "AlgebraicGeometry.ProEtaleWeilSheaf.powFunctor",
    "PR2122-DiagonalTraceFiniteEtaleIntegralBoundary": "AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_finiteEtale_integralBoundary",
}


for directory, target in CASES.items():
    case = ROOT / "Old" / directory
    original = (case / "Before.lean").read_text()
    output = case / "probes" / "HeadAudit.lean"
    output.parent.mkdir(exist_ok=True)
    output.write_text(original + SUFFIX.replace("AUDIT_TARGET", target))

proof_case = ROOT / "Old" / "PR1627-WeilSheafTransport"
(proof_case / "probes" / "GeneratedProofAudit.lean").write_text(
    (proof_case / "Before.lean").read_text()
    + (ROOT / "GeneratedProofSuffix.lean").read_text()
)
(proof_case / "probes" / "GeneratedProofPrefixes.lean").write_text(
    (proof_case / "Before.lean").read_text()
    + (ROOT / "GeneratedProofPrefixesSuffix.lean").read_text()
)

APP_CASES = {
    "PR1563-RawModuleScalarPullback": (
        "AlgebraicGeometry.Etale.rawModuleScalar_pullback_module_formula", 0
    ),
    "PR1625-TensorSheaf": (
        "AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorComparison_app_app_fac", 24
    ),
}
app_suffix = (ROOT / "ApplicationPrefixSuffix.lean").read_text()
for directory, (target, start) in APP_CASES.items():
    case = ROOT / "Old" / directory
    (case / "probes" / "ApplicationPrefixes.lean").write_text(
        (case / "Before.lean").read_text()
        + app_suffix.replace("AUDIT_TARGET", target).replace("AUDIT_START", str(start))
    )

result_case = ROOT / "Old" / "PR1625-TensorSheaf"
(result_case / "probes" / "ResultArguments.lean").write_text(
    (result_case / "Before.lean").read_text()
    + (ROOT / "ResultArgumentSuffix.lean").read_text()
)
(result_case / "probes" / "ResultLhsArguments.lean").write_text(
    (result_case / "Before.lean").read_text()
    + (ROOT / "ResultLhsSuffix.lean").read_text()
)
(result_case / "probes" / "NatTransMajor.lean").write_text(
    (result_case / "Before.lean").read_text()
    + (ROOT / "NatTransMajorSuffix.lean").read_text()
)

frame_suffix = (ROOT / "FrameAuditSuffix.lean").read_text()
for directory in [
    "PR1556-AmbientCounterexampleCoproducts",
    "PR1624-IntegersSheafHomologyTower",
    "PR2122-DiagonalTraceFiniteEtaleIntegralBoundary",
]:
    case = ROOT / "Old" / directory
    (case / "probes" / "ValueFrames.lean").write_text(
        (case / "Before.lean").read_text()
        + frame_suffix.replace("AUDIT_TARGET", CASES[directory])
    )

eq_case = ROOT / "Old" / "PR1563-RawModuleScalarPullback"
(eq_case / "probes" / "EqMprDomain.lean").write_text(
    (eq_case / "Before.lean").read_text()
    + (ROOT / "EqMprDomainSuffix.lean").read_text()
)
(eq_case / "probes" / "EqCompArguments.lean").write_text(
    (eq_case / "Before.lean").read_text()
    + (ROOT / "EqCompSuffix.lean").read_text()
)

iso_case = ROOT / "Old" / "PR1624-IntegersSheafHomologyTower"
(iso_case / "probes" / "IsoTransPrefixes.lean").write_text(
    (iso_case / "Before.lean").read_text()
    + (ROOT / "IsoTransPrefixSuffix.lean").read_text()
)
(iso_case / "probes" / "IsoDomainArguments.lean").write_text(
    (iso_case / "Before.lean").read_text()
    + (ROOT / "IsoDomainSuffix.lean").read_text()
)
(iso_case / "probes" / "IsoCompArguments.lean").write_text(
    (iso_case / "Before.lean").read_text()
    + (ROOT / "IsoCompArgumentsSuffix.lean").read_text()
)

closing_case = ROOT / "Old" / "PR1556-AmbientCounterexampleCoproducts"
(closing_case / "probes" / "ClosingSpine.lean").write_text(
    (closing_case / "Before.lean").read_text()
    + (ROOT / "ClosingSpineSuffix.lean").read_text()
)
(closing_case / "probes" / "ClosingPrefixes.lean").write_text(
    (closing_case / "Before.lean").read_text()
    + (ROOT / "ClosingPrefixesSuffix.lean").read_text()
)
(closing_case / "probes" / "ClosingProof.lean").write_text(
    (closing_case / "Before.lean").read_text()
    + (ROOT / "ClosingProofSuffix.lean").read_text()
)
(closing_case / "probes" / "ClosingId.lean").write_text(
    (closing_case / "Before.lean").read_text()
    + (ROOT / "ClosingIdSuffix.lean").read_text()
)
(closing_case / "probes" / "ClosingEqMp.lean").write_text(
    (closing_case / "Before.lean").read_text()
    + (ROOT / "ClosingEqMpSuffix.lean").read_text()
)
(closing_case / "probes" / "ClosingCongr.lean").write_text(
    (closing_case / "Before.lean").read_text()
    + (ROOT / "ClosingCongrSuffix.lean").read_text()
)
(closing_case / "probes" / "ClosingCongrDomain.lean").write_text(
    (closing_case / "Before.lean").read_text()
    + (ROOT / "ClosingCongrDomainSuffix.lean").read_text()
)
(closing_case / "probes" / "ClosingComp.lean").write_text(
    (closing_case / "Before.lean").read_text()
    + (ROOT / "ClosingCompSuffix.lean").read_text()
)
(closing_case / "probes" / "ClosingNatMajor.lean").write_text(
    (closing_case / "Before.lean").read_text()
    + (ROOT / "ClosingNatMajorSuffix.lean").read_text()
)
