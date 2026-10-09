/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import WeilConjectures.Mathlib.Topology.Category.TopCat.Limits.Pullbacks
public import WeilConjectures.Mathlib.Topology.Spectral.Basic

/-!
# Pullback

Ported from the `proetale` package (`Proetale.Topology.Preliminaries.Pullback`).
-/

@[expose] public section

universe u

open CategoryTheory TopCat Limits

variable {X Y S : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace S]
variable (f : C(X, S)) (g : C(Y, S))

variable {P : Type u} [TopologicalSpace P] {f' : C(P, Y)} {g' : C(P, X)}
    (pb : IsPullback (ofHom g') (ofHom f') (ofHom f) (ofHom g))

section pullback


variable [T2Space S]





end pullback

section IsPullback

variable {f g}

include f' g' pb

theorem CategoryTheory.IsPullback.t0Space [T0Space X] [T0Space Y] : T0Space P :=
  (homeoOfIso pb.isoPullback).symm.t0Space

variable [T2Space S]

theorem CategoryTheory.IsPullback.quasiSober [QuasiSober X] [QuasiSober Y] : QuasiSober P :=
  (homeoOfIso pb.isoPullback).symm.quasiSober

theorem CategoryTheory.IsPullback.compactSpace [CompactSpace X] [CompactSpace Y] : CompactSpace P :=
  (homeoOfIso pb.isoPullback).symm.compactSpace

theorem CategoryTheory.IsPullback.prespectralSpace [PrespectralSpace X] [PrespectralSpace Y] :
    PrespectralSpace P :=
  (homeoOfIso pb.isoPullback).symm.prespectralSpace

theorem CategoryTheory.IsPullback.spectralSpace [SpectralSpace X] [SpectralSpace Y] :
    SpectralSpace P :=
  (homeoOfIso pb.isoPullback).symm.spectralSpace

end IsPullback
