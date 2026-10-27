/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.AlgebraicGeometry.QuasiAffineRelativeSpecEmbedding
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec

/-!
# Composition of quasi-affine morphisms

Source: Stacks Project, Morphisms, Tag 01SN, lemma-composition-quasi-affine
(blueprint: lem-sfb-quasiaffine-morphism-composition).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The composite of two quasi-affine scheme morphisms is quasi-affine, without
finite-type, Noetherian, or separatedness assumptions on the schemes.
Source: Stacks Project, Morphisms, Tag 01SN, lemma-composition-quasi-affine
(blueprint: lem-sfb-quasiaffine-morphism-composition).

Proof:
1. Fix an affine open U of Z and write W = g⁻¹(U), E = f⁻¹(W). By
   def-nagata-quasi-affine-morphism, W is quasi-affine and the inverse image of
   each affine open under f is quasi-compact; hence f is quasi-compact by
   def-weil-finite-type-morphism. By lem-trf-quasi-affine-canonical-affine-embedding,
   W is quasi-compact and quasi-separated and its canonical map j to
   V = Spec Γ(W, 𝒪_W) is an open immersion. The node
   lem-weil-pbc-quasi-compact-morphism-preimage-qc-open makes E quasi-compact.
   V is affine, hence quasi-separated (lem-weil-pbc-affine-scheme-qcqs);
   lem-weil-pbc-qcqs-morphism-permanence makes j quasi-compact and quasi-separated.
2. The restriction E → W of f is quasi-affine: affine opens of W are affine
   opens of Y, with the same preimages (def-nagata-quasi-affine-morphism).
   By lem-trf-quasi-affine-relative-spec-embedding it factors as a quasi-compact
   open immersion i into R = Spec_W A, for a quasi-coherent 𝒪_W-algebra A.
3. Put A' = j_* A with the induced 𝒪_V-algebra structure. The underlying module
   is quasi-coherent by pqf-lem-pushforward-qcoh since j is quasi-compact and
   quasi-separated. By lem-weil-pbc-affine-morphism-relative-spec, clause (2),
   T = Spec_V A' is affine because V is affine.
4. Identifying W with its open image in V, the definition of direct image
   identifies A' restricted to W with A, on sections, restrictions, multiplication,
   and the structure-algebra action. Clauses (3) and (4) of
   lem-weil-pbc-affine-morphism-relative-spec identify R with the open subscheme
   T_W = π⁻¹(W) of T. Its inclusion is an open immersion (def-weil-open-immersion).
5. Composing i with T_W → T identifies E with an open subscheme of the affine
   scheme T: an open subset of an open subset is open, and the sheaf maps are
   restriction isomorphisms (def-weil-open-immersion). Step 1 makes E quasi-compact.
   Thus the preimage of every affine open U under the composite is quasi-affine,
   which is exactly def-nagata-quasi-affine-morphism. -/
theorem isQuasiAffineHom_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsQuasiAffineHom f] [IsQuasiAffineHom g] : IsQuasiAffineHom (f ≫ g) := by
  sorry

end AlgebraicGeometry
