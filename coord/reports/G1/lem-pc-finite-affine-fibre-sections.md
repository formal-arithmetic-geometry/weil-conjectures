## Worker report

The module states `AlgebraicGeometry.finite_affine_fibre_sections`, with a `sorry`
proof. The declaration uses local notation for the actual affine morphism `f`,
base stalk `R`, direct-image stalk `P`, and residue field `K`.

- `A B : Type u`, `[CommRing A]`, `[CommRing B]`, `[Algebra A B]` give the
  commutative ring and its algebra. `[Module.Finite A B]` is the finite-algebra
  hypothesis. `p : Spec (CommRingCat.of A)` is the point of the affine base.
- `f` is `Spec.map (CommRingCat.ofHom (algebraMap A B))`, with source `Spec B`
  and target `Spec A`. `R` is the actual structure-sheaf stalk at `p`; `P` is
  the actual pushforward-structure-sheaf stalk at `p`; `K` is `residueField p`.
  The three local algebra instances are induced by the sheaf map and residue
  map, so `(P ⊗[R] K)` is the exact stalk tensor in the node.
- The equivalence `e : (P ⊗[R] K) ≃+* Γ((f).fiber p, ⊤)` expresses that the
  canonical map is an isomorphism. Its values on `b ⊗ 1` and `1 ⊗ k` agree
  with those of `g`, fixing the canonical map rather than an arbitrary ring
  equivalence.
- The equivalence `g : (B ⊗[A] K) ≃+* Γ((f).fiber p, ⊤)` expresses the
  affine description. The final two equations identify its values on `b ⊗ 1`
  and `1 ⊗ k` with the maps on global sections induced by the two fibre
  projections. Since `K` is the residue field of the stalk, this is also the
  stated `B ⊗_A A_s/m_s A_s` description.

Dependencies used: `AlgebraicGeometry.Scheme` and `.Hom` in
`Mathlib.AlgebraicGeometry.Scheme`; `AlgebraicGeometry.Spec` and `Spec.map` in
the same module; `Scheme.residueField` in
`Mathlib.AlgebraicGeometry.ResidueField`; `IsFinite` in
`Mathlib.AlgebraicGeometry.Morphisms.Finite` is represented by
`[Module.Finite A B]` for this affine morphism; `AlgebraicGeometry.pullbackSpecIso`
in `Mathlib.AlgebraicGeometry.Pullbacks` gives the affine fibre description.
The module also uses `StructureSheaf.toPushforwardStalk` in
`Mathlib.AlgebraicGeometry.Spec` and `Scheme.Hom.fiber` in
`Mathlib.AlgebraicGeometry.Fiber`.

Edge cases: `A` may be the zero ring (then `Spec A` has no point, so the
quantification over `p` is vacuous); `B` may be the zero ring (empty fibre);
the residue field may have arbitrary characteristic; no bound is placed on
the size of the rings beyond the shared Lean universe `u`. Finiteness is
included even though the affine calculation does not use it.

Searches: `msearch.py leanfinder` for "sections of affine fibre of finite
morphism Spec B over Spec A at prime tensor residue field" found fibre
constructions but no sections isomorphism. `msearch.py loogle` for
`Scheme.Hom.fiber, Scheme.Pullback.Triplet.tensor` had no hit. `msearch.py grep`
for `fiber.*(sections|Γ)|pushforward.*stalk` found the localization map,
not this theorem. `rg` over Mathlib, WeilConjectures, and Sheaf modules found
no exact declaration; `rg` of `dag/lean_names_upstream.json` found no name.

The local Stacks source checkout is absent. The online Stacks Tag 02KB is the
finite locally free equivalence, not this particular affine fibre calculation;
the node cites its proof context rather than a verbatim Stacks lemma. This
source-place discrepancy should be reviewed by the second reader.

## Second reading by G1

The node introduces a commutative ring `A`, a finite `A`-algebra `B`, the affine
schemes `V = Spec(A)` and `X = Spec(B)`, and a point `s` of `V` with residue
field `κ(s)`. The Lean binders `A B : Type u`, `[CommRing A]`, `[CommRing B]`,
`[Algebra A B]`, `[Module.Finite A B]`, and
`p : Spec (CommRingCat.of A)` render these objects and hypotheses. The shared
universe is the project convention for affine schemes and does not alter the
mathematical cases represented by the declaration. The local notation `f` is
the induced `Spec.map` morphism, while `R`, `P`, and `K` are respectively the
base stalk, direct-image structure-sheaf stalk, and residue field.

The conclusion's canonical stalk-tensor-to-fibre-sections isomorphism is rendered
by the ring equivalence `e : (P ⊗[R] K) ≃+* Γ((f).fiber p, ⊤)`. The affine
description `B ⊗_A κ(s)` is rendered by `g : (B ⊗[A] K) ≃+* Γ((f).fiber p, ⊤)`.
The first conjunction clause identifies `e` and `g` on every `b ⊗ 1`; the second
does so on every `1 ⊗ k`; the third identifies `g(b ⊗ 1)` with the map induced by
the fibre projection from `Spec B`; and the fourth identifies `g(1 ⊗ k)` with the
map induced by the fibre's morphism to `Spec K`. Quantifiers and conjunction
order match the node exactly, and no additional hypotheses occur.

Edge cases checked: the zero ring `A` has no points, so the point-indexed theorem
is vacuous; the zero ring `B` gives the empty affine fibre; arbitrary residue-field
characteristic and `n = 0`-type rank cases are not restricted; and the tensor
equivalences permit the zero algebra. The declaration imposes no finiteness beyond
the node's finite-algebra hypothesis.

Searches were repeated with LeanFinder/Loogle-style searches for affine fibre
sections and pushforward stalk tensor products, and with `rg` over Mathlib,
`WeilConjectures`, `Sheaf`, and `dag/lean_names_upstream.json`; only the generic
fibre and affine pullback declarations were found, with no exact theorem.

Mismatch found and changed: the theorem docstring had the source summary but not
the node's step-by-step proof, violating the stage-2 documentation requirement.
It now records the three proof steps and their dependency nodes. The Lean
statement and node `lean.statement` were otherwise already verbatim and correct;
the source-place discrepancy noted in the worker report belongs to the node and
was not silently changed.
