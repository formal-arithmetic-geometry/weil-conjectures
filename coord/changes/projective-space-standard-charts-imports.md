# projectiveSpaceStandardCharts imports
## Reason
The proof was decomposed into three component modules. The original large proof-only imports were removed from the item and replaced by the component modules; the public chart declarations remain available through the explicit public `OfSections` import.
## Old
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts;
import Sheaf.AlgebraicGeometry.Modules.InvertiblePullbackTensor;
import Sheaf.AlgebraicGeometry.ProjectiveSpaceTwistGluedIdentification;
import Sheaf.AlgebraicGeometry.ProjectiveSpaceTwistingSheafCharts;
import Sheaf.AlgebraicGeometry.TensorPullback;
import Sheaf.Paper.NonvanishingSectionTrivializes;
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
## New
Replace the public Charts import with public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfSections. Import ProjectiveSpaceStandardChartsPullback, ProjectiveSpaceStandardChartsNonvanishing and ProjectiveSpaceStandardChartsAffine privately from Sheaf.AlgebraicGeometry. Remove the six former proof-only imports listed above.
## Users
| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts | Y3 | imports follow the decomposed proof |
| Sheaf.AlgebraicGeometry.CompleteLinearSystemClosed | unclaimed | Original source compiles against the delivered modules; statement unchanged |
| Sheaf.AlgebraicGeometry.ProjectiveAmpleInvertible | M4 | Original source compiles against the delivered modules; statement unchanged |
| Sheaf.AlgebraicGeometry.ProjectiveLinePowerAffineCharts | unclaimed | Original source compiles against the delivered modules; statement unchanged |
## Status
landed 20261013T000049-L-2232776 2026-10-13 (merge of deliver/Y3/Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts)
