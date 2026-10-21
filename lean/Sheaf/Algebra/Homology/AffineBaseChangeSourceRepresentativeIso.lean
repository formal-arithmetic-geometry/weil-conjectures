/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V8
-/
module

public import WeilConjectures.Algebra.Homology.AffineBaseChangeSourceRepresentativeIso
public import Sheaf.Algebra.Homology.KFlat

/-! # Independence of the source-only stalk comparison from its representative

Source: Stacks Project, Tags 06Y6, 08IB and 0DJ8, equation-bc.
(blueprint: lem-pc-affine-base-change-source-representative-iso).

Re-export the proved source implementation at the historical module path, so the
representative-independence theorem has a single declaration provider. The K-flat
import preserves the historical predicate `CochainComplex.IsAcyclicTensorKFlat`,
whose defining acyclic tensor formula is identical to `CochainComplex.IsKFlatTensor`.
-/

@[expose] public section
