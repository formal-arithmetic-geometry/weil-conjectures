/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A7
-/
module

public import Sheaf.Paper.ConstantExtensionSheetHeartData
import Sheaf.Paper.IsomorphismFieldTransport
import Sheaf.Paper.FiniteClopenDerivedDecomposition
import Sheaf.Paper.IntegralPullbackComposition
import Sheaf.Paper.PullbackIdentitiesScalarExtension

/-! # Common-stage cyclic sheet equivalences

Source: Deligne, Weil II, pp. 150--152; Stacks Project, Tags 04TS and 0D6D.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (m : ℕ) (hm : 1 ≤ m)
variable (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]

variable (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The coefficient-stage sheet equivalences pass to the actual common-stage category.
Source: Deligne, Weil II, pp. 150--152; Stacks Project, Tags 04TS and 0D6D
(blueprint: lem-zl-constant-extension-sheet-common-stage-equivalences).

Proof: represent the finitely many components over one common finite coefficient
field. The rational product equivalence from the coefficient clauses has an
inverse: transport to the clopen components by the inverse coordinate maps and
glue. The normalized scalar comparisons make this inverse independent of further
extension and make its unit and counit descend to common-stage arrows. Thus the
actual common-stage pullbacks form an equivalence. Both standard halves are
detected componentwise: one direction is stagewise, and in the other direction
the finitely many witnesses can be extended to a single field and glued there.
These inverse functors restrict to the full hearts with the same arrows, hence
the restriction and each component preserve finite limits and colimits.
The stage comparison is the literal pullback-on-representatives identification;
choose its identity components, giving stage_normalization. Stagewise exact
inverse image and the standard truncation uniqueness give the cohomology
comparison. Apply isomorphism field transport also to geometric Frobenius and its
inverse to obtain the Frobenius equivalence on hearts and its exactness.
Finally give each clopen component the inherited residue units from the fibre.
For G.coordinate and G.opens.ι restrict the actual pullbacks to the hearts. The
former is an equivalence by isomorphism transport, and its finite coefficient
clauses are the same termwise transport with singleton index. The latter is
exact component restriction. The compositor for G.factor identifies their
composite with the product-heart projection. This gives all coordinate factors,
including the equivalence on ambient common-stage categories. All constructions
retain the published integral compositors after rationalization, so no new scalar
or pullback normalization is chosen. -/
theorem constantExtensionSheetCommonStageEquivalences
    (G : ZlSheetGeometry D m hm X₀)
    (hcoeff : ZlSheetCoefficientClauses D m hm X₀ l hl) :
    Nonempty (ZlSheetCommonClauses D m hm X₀ l hl Ω G) := by sorry

end WeilConjectures
