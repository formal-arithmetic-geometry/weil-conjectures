/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Jacobson.Ring
import Sheaf.AlgebraicGeometry.AmpleFiniteSetAffine
import WeilConjectures.AlgebraicGeometry.InvariantAffineNeighbourhoods
import Sheaf.AlgebraicGeometry.InvariantAffineDescentGluing
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Sheaf.AlgebraicGeometry.InvertibleAffineLimitDescent
import Sheaf.AlgebraicGeometry.AmpleAffineLimitDescent
import Sheaf.AlgebraicGeometry.SchemeRelativeAmpleBaseChange
import Sheaf.TraceFormula.SchemeRelativeAmpleAffineCover
import WeilConjectures.AlgebraicGeometry.FpqcRefinementReflectsEffectivity

/-! # Effective descent over an arbitrary extension of fields

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, Section 6.5, Theorem 1,
first paragraph of the proof, printed p.160, and Section 6.2, Example B.
(blueprint: lem-sfb-field-ample-scheme-datum-effectivity).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace CategoryTheory.Over.DescentDatum

/-- Every descent datum on a finite-type scheme with an ample invertible module is effective
along an arbitrary extension of fields. The ample module is not equipped with a descent datum.

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, Section 6.5, Theorem 1,
proof, printed p.160, and Section 6.2, Example B.
(blueprint: lem-sfb-field-ample-scheme-datum-effectivity).

Proof:
1. We first check coverings that will occur below. For any nonzero $k$-algebra $A$, the
   field-algebra lemma makes $k\to A$ faithfully flat. The ring-to-scheme flatness criterion and
   faithful-flat spectrum surjectivity make $\operatorname{Spec}A\to\operatorname{Spec}k$ flat and
   surjective. Its source is affine, so the single affine open $\operatorname{Spec}A$ verifies the
   affine-cover condition in the definition of an fpqc covering. This applies to $A=L$, to every
   $k$-subalgebra $C\subseteq L$, and to every residue field of such a $C$. Uses:
   lem-sfb-nonzero-field-algebra-faithfully-flat, lem-weil-pbc-flat-ring-map-iff-flat-affine,
   lem-weil-pbc-faithfully-flat-surjective-spectrum, def-weil-pbc-fpqc-covering.

2. Prove first the finite-extension case, for an arbitrary finite field extension $E/k$ and an
   $E$-scheme $V$ with an ample invertible module and a descent datum. A finite $k$-basis of $E$
   generates it as a module and also as an algebra. The affine-local-target criterion and the
   definition of a finite morphism therefore make $p:\operatorname{Spec}E\to\operatorname{Spec}k$
   finite. The field $k$ is Noetherian (its only ideals are $0,k$); the finite-type-algebra
   finite-presentation lemma makes $E$ finitely presented over $k$. Thus $p$ is locally of finite
   presentation by the affine definition. Step 1 supplies flatness and surjectivity. The ample
   finite-set lemma puts every finite subset of $V$ inside an affine open. Apply invariant-affine
   neighbourhoods to this datum and $p$: every point has a transport-invariant affine
   neighbourhood over an affine open of $\operatorname{Spec}k$. The invariant-affine gluing
   theorem now makes the datum effective. This proves the finite-extension case without
   separability or a datum on the ample module. Uses: pqf-lem-affine-local-target,
   def-weil-finite-integral-morphism, lem-weil-pbc-finite-type-noetherian-finite-presentation,
   def-sbc-locally-finite-presentation, lem-sc-ample-finite-set-affine,
   lem-pd-invariant-affine-neighbourhoods, lem-pd-invariant-affine-descent-gluing.

3. Return to $X'/L$. A field is Noetherian since each ideal is either zero or the whole field, so
   $\operatorname{Spec}L$ is Noetherian. Finite-type preservation of Noetherianness makes $X'$
   Noetherian; locally Noetherian quasi-separatedness makes it quasi-separated. On a finite affine
   finite-type cover, the finite-type-algebra finite-presentation lemma gives finitely presented
   $L$-algebras. The structure morphism $X'\to\operatorname{Spec}L$ is quasi-compact by the
   definition of finite type, and quasi-separated by qcqs morphism permanence (1), because its
   source $X'$ is quasi-separated. Hence $X'\to\operatorname{Spec}L$ is locally of finite
   presentation, quasi-compact and quasi-separated, that is, of finite presentation. This checks
   the input to spreading out; finite type alone over a general base would not suffice. Uses:
   lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-locally-noetherian-quasi-separated,
   lem-weil-pbc-finite-type-noetherian-finite-presentation, def-sbc-locally-finite-presentation,
   lem-weil-pbc-qcqs-morphism-permanence.

4. Let $I$ be the inclusion-ordered set of finitely generated $k$-subalgebras $C\subseteq L$. It
   is small in the universe of $L$, nonempty (it contains $k$), and directed: adjoining both
   finite sets of generators gives a common upper bound. Its union is $L$, since any element lies
   in the subalgebra it generates. The affine-limit theorem identifies $\operatorname{Spec}L$ with
   $\varprojlim_C\operatorname{Spec}C$. All stages are affine and hence qcqs, and all transition
   maps are affine by the affine-local-target criterion. Apply clause (1) of spreading out to
   obtain a finitely presented $Y_0\to\operatorname{Spec}C_0$ and a specified $L$-isomorphism
   $(Y_0)_L\simeq X'$. For $C\supseteq C_0$ put $Y_C=(Y_0)_C$. These schemes are qcqs with affine
   transition maps, and have limit $X'$: the universal property of the fibre product identifies
   compatible maps to the $Y_C$ with a map to $Y_0$ and a compatible family of maps to the
   $\operatorname{Spec}C$. Uses: lem-weil-pbc-limit-affine-transition, thm-pd-spreading-out,
   pqf-lem-affine-local-target, def-sbc-locally-finite-presentation,
   lem-weil-pbc-affine-scheme-qcqs, lem-weil-pbc-affine-morphism-permanence,
   lem-weil-pbc-qcqs-morphism-permanence.

5. Apply invertible-module limit descent to $X'=\varprojlim_{C\supseteq C_0}Y_C$ and the given
   ample module $M'$ to obtain an invertible module $M_{C_1}$ whose pullback is $M'$. Apply
   ample-module limit descent to this module on the same tail system. After increasing $C_1$ to
   $C_2$, its pullback $M_{C_2}$ is ample on $Y_{C_2}$. Any later enlargement still has an ample
   module, by relative ample base change: apply the relative-ample affine-cover criterion to the
   singleton cover of $\operatorname{Spec}C_2$. Its quasi-compactness hypothesis holds because
   $Y_{C_2}$ is finitely presented over this base. Then apply relative ample base change and take
   the whole later affine base as its affine open. No datum on $M'$ or on any $M_C$ has been used
   or constructed. Uses: lem-trf-invertible-affine-limit-descent,
   lem-trf-ample-affine-limit-descent, lem-trf-scheme-relative-ample-base-change,
   lem-trf-scheme-relative-ample-affine-cover.

6. We descend the scheme datum itself, retaining the ample model from step 5. For $n=2,3$, the
   rings $C^{\otimes_k n}$ have colimit $L^{\otimes_k n}$: maps out of these colimits are
   compatible $n$-tuples of $k$-algebra maps out of the $C$, equivalently $n$-tuples of maps out
   of $L$, which is the tensor-product universal property. Taking a tail $C\supseteq C_2$ leaves
   the colimit unchanged. The affine-limit theorem supplies the corresponding inverse limits of
   spectra. Over $\operatorname{Spec}(C^{\otimes_k2})$, the two pullbacks of $Y_C$ are of finite
   presentation, being base changes of $Y_0$. Apply clause (2) of spreading out separately to the
   given datum isomorphism $\varphi$ over $L\otimes_kL$ and to its inverse. Directedness puts both
   descended maps $a,b$ over a common $C$. Their composites pull back to the identities; two
   applications of clause (3), followed by a common enlargement of $C$, make $ba=1$ and $ab=1$.
   Thus $a$ is an isomorphism with precisely the prescribed pullback $\varphi$. Uses:
   lem-weil-pbc-limit-affine-transition, thm-pd-spreading-out, def-pd-descent-datum,
   lem-weil-pbc-qcqs-morphism-permanence.

7. Over the triple tensor base $\operatorname{Spec}(C^{\otimes_k3})$, compare the two maps
   $a_{02}$ and $a_{12}a_{01}$. Their domains and codomains are pullbacks of $Y_C$, hence of
   finite presentation. Their pullbacks to $\operatorname{Spec}(L^{\otimes_k3})$ agree by the
   given cocycle. Clause (3) of spreading out gives a further $C$ on which $a_{02}=a_{12}a_{01}$.
   The inverse equations persist under base change. We now have a finitely presented scheme
   $Y_C/C$, an ample invertible module on it, and a genuine descent datum $D_C$ relative to
   $\operatorname{Spec}C\to\operatorname{Spec}k$ whose pullback to $L$ is the original datum. In
   particular the limit argument has descended the equations, not just the underlying isomorphism.
   Uses: thm-pd-spreading-out, def-pd-descent-datum, lem-weil-pbc-qcqs-morphism-permanence.

8. Choose a maximal ideal $\mathfrak m$ of the nonzero finitely generated $k$-algebra $C$, and put
   $E=C/\mathfrak m$. Zariski's lemma says $E/k$ is finite. Pull back $Y_C,D_C$ along
   $h:\operatorname{Spec}E\to\operatorname{Spec}C$. The singleton affine-cover criterion, followed
   by relative ample base change, gives an ample module on $Y_E$; $Y_C/C$ is finitely presented,
   so is quasi-compact as required by that criterion. The finite-extension case of step 2 makes
   $D_E$ effective. Both $\operatorname{Spec}C\to\operatorname{Spec}k$ and
   $\operatorname{Spec}E\to\operatorname{Spec}k$ are singleton fpqc covers by step 1, and their
   triangle with $h$ commutes. The square defining $Y_E$ is cartesian, and its datum is the
   pullback of $D_C$. Apply fpqc refinement reflection of effectivity to deduce that $D_C$ is
   effective. This theorem does not require $h$ itself to be flat. Let $X/k$ and $X_C\simeq Y_C$
   realize $D_C$. Base changing this isomorphism along $C\subseteq L$ gives $X_L\simeq X'$; its
   datum is the prescribed one because $D_C$ was descended together with $\varphi$ and its
   cocycle. This is exactly effectivity as defined, for the original arbitrary extension $L/k$.
   Uses: lem-weil-pbc-zariski-lemma, lem-trf-scheme-relative-ample-base-change,
   lem-galois-fpqc-refinement-reflects-effectivity, def-pd-descent-datum,
   lem-trf-scheme-relative-ample-affine-cover.
-/
theorem isEffective_of_field_extension_isAmple
    (k L : Type u) [Field k] [Field L] [Algebra k L]
    (X : Over (Spec (CommRingCat.of L)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (M : X.left.Modules) [M.IsInvertible] (hM : Scheme.Modules.IsAmple X.left M)
    (D : Over.DescentDatum (Spec.map (CommRingCat.ofHom (algebraMap k L))) X) :
    D.IsEffective := by
  sorry

end CategoryTheory.Over.DescentDatum
