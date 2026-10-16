/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.FiniteSplitReplacementAttachmentConstruction
import Sheaf.Paper.FiniteSplitReplacementStage
import WeilConjectures.AlgebraicGeometry.FiniteSplitEtaleHypercover

/-! Split hypercover data on the explicitly constructed simplicial attachment. -/
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.SchemeSplitAttachment

/-- Source: Stacks, Hypercoverings, 0DAV, split extension; 01GJ, matching covers.

Use the old nondegenerate schemes and inclusions below the new degree, and use
V with the left coproduct injection in the top degree. In a lower degree every
epi has target degree at most that degree; remove the impossible top labels and
use U.splitting. In the top degree an epi to itself is the identity. Separate
this unique new label from all labels of target degree at most n. Their cofan
is the binary coproduct of V and the coproduct indexed by Labels n (n+1).
The identity label gives coprod.inl. For each lower label, attachmentMap_epi
and attachEpi_fac with the identity old label give exactly oldInclusion.
Therefore the canonical coproduct colimit proves the top splitting cofan.

Keep each old matching scheme, projection and matching map. The new matching
scheme is Q.M. Every simplex of degree below n+1 lies in the old truncation,
so Q.pi gives all its projections; Q.naturality gives their equations. Its
universal property is Q.universal, after transporting along the old restriction
of attachedSimplicial. Apply that universal property to the cone of top face
operators attachFace to define the matching map. This cone is natural by
attachFace_naturality. Uniqueness in Q.universal, after precomposing with the
new inclusion coprod.inl, identifies its restriction with b. Since b is
surjective, the matching map is surjective. This choice is determined uniquely
by all projections, not an arbitrary witness of mere existence.

Use hf for the new nondegenerate finiteness witness and retain every old witness.
Every lower field is literally retained; the proved restriction identity of
attachedSimplicial identifies the simplicial fields. Dependent structure
extensionality, uniqueness of colimit witnesses, and proof irrelevance for
proposition-valued fields yield the exact restriction equality stated below.
This theorem has no refinement target K:
the simplicial object and all its operator laws are already constructed.
(blueprint: lem-weil-pbc-finite-split-replacement-attachment-structure) -/
theorem exists_attached_split_structure
    {X : Scheme.{u}} {n : ℕ} (U : TruncatedFiniteSplitEtaleHypercover X n)
    (V : X.Etale) (Q : ReplacementBoundary U) (b : V ⟶ Q.M)
    (hc : Surjective b.left)
    (hf : ∃ (k : ℕ) (W : Fin k → X.Etale) (ι : ∀ i, W i ⟶ V),
      Nonempty (IsColimit (Cofan.mk V ι)) ∧
        ∀ i, CompactSpace (W i).left ∧ QuasiSeparatedSpace (W i).left ∧
          LocallyOfFinitePresentation (W i).hom ∧ QuasiCompact (W i).hom ∧
            QuasiSeparated (W i).hom) :
    ∃ U' : TruncatedFiniteSplitEtaleHypercover X (n + 1),
      U'.simplicial = attachedSimplicial U V Q b ∧
        U'.restrict n (Nat.le_succ n) = U := by
  sorry

end AlgebraicGeometry.SchemeSplitAttachment
