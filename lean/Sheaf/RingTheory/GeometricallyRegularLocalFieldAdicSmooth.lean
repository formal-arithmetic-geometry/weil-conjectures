module

public import WeilConjectures.RingTheory.GRing
public import WeilConjectures.RingTheory.FormallySmoothAdic
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.FieldTheory.SeparablyGenerated
import WeilConjectures.FieldTheory.SeparableExtension
import WeilConjectures.RingTheory.GeometricallyRegularH1Injective
import WeilConjectures.RingTheory.DifferentialsInjectiveOfH1CotangentInjectiveCharP
import Mathlib.RingTheory.Kaehler.Basic
import WeilConjectures.RingTheory.FormallySmoothAdicSmallKernelCriterion
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Adic formal smoothness of geometrically regular local field algebras

Source: Stacks Project, More on Algebra, Theorem Tag 07EL, implication (1) to (2),
using regularity in characteristic zero and (4) to (5) to (2) in positive characteristic.
(blueprint: lem-sfb-geometrically-regular-local-field-adic-smooth)
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Algebra

/-- A geometrically regular Noetherian local algebra over any field is formally smooth
for the adic topology of its unique maximal ideal. No finite-type, completeness,
characteristic, or residue-field separability assumption is needed.

Source: Stacks Project, More on Algebra, Theorem Tag 07EL, implication (1) to (2).
(blueprint: lem-sfb-geometrically-regular-local-field-adic-smooth)

Proof, following the node's five steps:
1. Set `n = IsLocalRing.maximalIdeal B` and `K = B / n`. The identity finite purely
   inseparable extension in def-weil-pbc-g-ring gives regularity of `B`, and hence
   regular locality. In characteristic zero, every finitely generated intermediate
   field of `K/k` has a separating transcendence basis by
   lem-weil-pbc-perfect-field-separating-basis. Thus `K/k` is separable in the sense
   of def-weil-pbc-separable-field-extension, and
   lem-sfb-regular-local-separable-residue-adic-smooth proves the conclusion.
2. In characteristic `p > 0`, lem-weil-pbc-geometrically-regular-h1-injective gives
   regular locality and injectivity of the canonical map `H1(L_{K/k})` to `n/n^2`.
   Apply lem-weil-pbc-h1-injective-differentials-injective-char-p to obtain the
   injective canonical comparison from `Omega(k/F_p)` tensored with `K` to
   `Omega(B/F_p)` tensored with `K`. These are the universal differential modules
   of def-weil-pbc-kahler-differentials.
3. Apply lem-weil-pbc-fs-adic-small-kernel-criterion. Fix a square-zero ideal `J`
   of a `k`-algebra `D`, and a map `g : B -> D/J` killing `n^r`, with `r >= 1`,
   whose representatives of `g(n)` annihilate `J`. The `B`-module action on `J`
   defined using lifts through `g` is independent of those lifts since `J^2 = 0`;
   it factors through the field `K`. Frobenius fixes the prime field `F_p`, so
   lem-weil-pbc-perfect-field-separating-basis and
   def-weil-pbc-separable-field-extension show that `K/F_p` is separable.
   Lemma lem-sfb-regular-local-separable-residue-adic-smooth over `F_p` gives an
   `F_p`-algebra lift `psi : B -> D` of `g`.
4. If `i : k -> B` and `phi : k -> D` are the structure maps, their defect
   `delta = psi i - phi` takes values in `J`. Expanding products and using
   `J^2 = 0` shows that it is an `F_p`-derivation. By
   def-weil-pbc-kahler-differentials it factors through `Omega(k/F_p)`, and then
   through its scalar extension to `K`. Transfer this linear map to the image
   of the injection of step 2. If that image is the whole space, it already
   defines the extension; otherwise choose a vector outside it and apply
   lem-sfb-linear-map-extension-prescribed-value with prescribed value zero.
   Composing the resulting extension with `d b` tensored with `1` gives a
   derivation `Delta : B -> J` satisfying `Delta i = delta`.
5. Set `f = psi - Delta`. Additivity, preservation of `1`, the derivation identity
   and `J^2 = 0` show that `f` is a ring map. Its reduction is `g`, and
   `f i = psi i - delta = phi`, so it is a `k`-algebra lift. The small-kernel
   criterion proves the required property of def-weil-pbc-formally-smooth-adic.
   Any lift maps `n^r` into `J` and therefore kills `n^(2*r)`, so it is continuous.
-/
theorem formallySmoothAdic_of_isGeometricallyRegular (k : Type u) (B : Type v)
    [Field k] [CommRing B] [Algebra k B] [IsNoetherianRing B] [IsLocalRing B]
    (hB : IsGeometricallyRegular k B) :
    FormallySmoothAdic k B (IsLocalRing.maximalIdeal B) := by
  sorry

end Algebra
