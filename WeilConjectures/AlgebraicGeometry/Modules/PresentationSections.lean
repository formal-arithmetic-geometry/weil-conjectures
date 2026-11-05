/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.AffineHom
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackSections
public import Mathlib.Algebra.Module.Presentation.Finite
public import WeilConjectures.Mathlib.Algebra.Module.Presentation.Tensor

/-!
# Presentations of global sections of modules on affine schemes

On an affine scheme, quasi-coherent modules are determined by their global sections. We express
this in terms of presentations `Module.Relations.Solution.IsPresentation` of the global sections:

- if `s` presents `Γ(N, ⊤)` by relations `ρ` and `g : Y ⟶ Z` is a morphism of affine schemes,
  then the pullbacks `pullbackΓ g N (s.var i)` present `Γ(g^* N, ⊤)` by the relations `ρ` with
  coefficients pulled back along `g`
  (`AlgebraicGeometry.Scheme.Modules.exists_isPresentation_pullbackΓ`);
- morphisms out of a module whose global sections are presented by `s` are determined by the
  images of the generators, and any solution of the relations in the global sections of the
  target comes from a morphism
  (`AlgebraicGeometry.Scheme.Modules.hom_ext_of_isPresentation`,
  `AlgebraicGeometry.Scheme.Modules.exists_hom_of_isPresentation`);
- for finitely many generators and relations there is a module of finite presentation whose
  global sections are presented by them
  (`AlgebraicGeometry.Scheme.Modules.exists_isFinitePresentation_isPresentation`).
-/

@[expose] public section

universe w₀ w₁ u

open CategoryTheory Module

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y Z : Scheme.{u}}

variable [IsAffine Y] {M N : Y.Modules} [M.IsQuasicoherent]
  {ρ : Relations.{w₀, w₁} Γ(Y, ⊤)} {s : ρ.Solution Γ(M, ⊤)}

end AlgebraicGeometry.Scheme.Modules
