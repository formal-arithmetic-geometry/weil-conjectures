/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionChartComparisonIso

/-! # Affine chart comparison for tensor resolutions

Re-export the source-library construction of
`AlgebraicGeometry.tensorResolutionChartComparisonIso`. Keeping a single implementation
avoids duplicate declarations after the source-library sync. The comparison still uses the
specified chart augmentation and the four-map comparison through the restricted second
K-flat resolution.
-/

@[expose] public section
