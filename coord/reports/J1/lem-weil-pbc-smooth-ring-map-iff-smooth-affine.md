## Worker report

Existing declaration: `AlgebraicGeometry.HasRingHomProperty.Spec_iff`, in
`Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties`, lines 360–364.
No module is delivered, because its specialization is exactly this node's statement.
The verbatim source signature is recorded in `lean.statement`; its ambient binders are
`{P : MorphismProperty Scheme.{u}}`, the ring property `Q`, and
`[HasRingHomProperty P Q]`. Specialize `P := @AlgebraicGeometry.Smooth.{u}` and
`Q := RingHom.Smooth`. Mathlib supplies this instance in
`Mathlib.AlgebraicGeometry.Morphisms.Smooth`, lines 71–78, without an additional
mathematical hypothesis. These property parameters select the two recorded notions;
they do not restrict the rings or their homomorphism.

Hypotheses and clauses, individually:

- Commutative rings R and S: `{R S : CommRingCat.{u}}`, containing their CommRing
  structures. A ring homomorphism φ is `{φ : R ⟶ S}`, with underlying ring map `φ.hom`.
  Bundling does not require a domain, field, Noetherian ring, or a nonzero ring.
- The induced affine morphism is `AlgebraicGeometry.Spec.map φ : Spec S ⟶ Spec R`,
  precisely the dependency's contravariant spectrum morphism.
- Smoothness of this scheme morphism is `Smooth (Spec.map φ)` after selecting P.
  This uses the current recorded declaration of `def-sbc-smooth-morphisms`, which
  explicitly identifies Mathlib's affine-local Smooth with local finite presentation
  and formal smoothness by Stacks 02H6.
- Smoothness of the ring map is `RingHom.Smooth φ.hom` after selecting Q. Reading
  `Mathlib.RingTheory.RingHom.Smooth` lines 73–91 shows that this is exactly
  `Algebra.Smooth R S` for the algebra structure induced by φ, the declaration of
  `def-weil-pbc-smooth-ring-map`.
- Finite presentation is `Algebra.Smooth.finitePresentation`. Vanishing of H1 is
  `Algebra.FormallySmooth.subsingleton_h1Cotangent`; projectivity of Ω is
  `Algebra.FormallySmooth.projective_kaehlerDifferential`. Finite presentation implies
  essential finite type, and Smooth/Basic.lean line 189 gives finite presentation of Ω,
  hence its finiteness. These are the ring predicate's three clauses, not extra assumptions.
- The biconditional `↔` gives both directions with the same rings and the same map.

Dependency declarations read and used:

- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map` in
  `Mathlib.AlgebraicGeometry.Scheme`, including their docstrings and full definitions.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth` in
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, including its affine-open condition.
- `def-weil-pbc-smooth-ring-map`: `Algebra.Smooth` in
  `Mathlib.RingTheory.Smooth.Basic`, including its FormallySmooth and FinitePresentation
  fields and the underlying FormallySmooth definition. The ring-hom wrapper above
  supplies exactly this definition for the map's induced algebra structure.

Source checked: the local literature/stacks-project TeX files are absent on this machine,
so I opened https://stacks.math.columbia.edu/tag/01V6 and
https://stacks.math.columbia.edu/tag/02H6. The first identifies affine-local smoothness
with smooth ring maps on affine opens; the second identifies it with local finite
presentation plus formal smoothness. They validate the equivalence explicitly recorded
in the smooth-morphism dependency. The stage-1 search verdict in this item predates that
record and does not require a duplicate lifting-based Smooth predicate now.

Edge cases checked before selecting the existing declaration: zero rings and empty
spectra are admitted (CommRingCat has no Nontrivial restriction); identity maps and
polynomial algebras fit both predicates; arbitrary characteristic is admitted; no finite
type, flatness, or smoothness premise has been imposed. Rings in different universes
can both be placed in their maximum universe, so bundling at a common u excludes no
ring pair. There is no quantification over test objects in a smaller universe.

Searches:

- msearch.py leanfinder: "A ring homomorphism is smooth if and only if its induced
  morphism of affine spectra is smooth" returned eight hits, including the Smooth
  HasRingHomProperty instance, isSmooth_iff, and RingHom.Smooth.toAlgebra.
- msearch.py loogle: "AlgebraicGeometry.HasRingHomProperty.Spec_iff, RingHom.Smooth"
  returned no hits.
- msearch.py grep: "Spec_iff|smooth.*[Ss]pec|[Ss]mooth.*[Ss]pec" in
  AlgebraicGeometry/Morphisms returned 25 hits, including the exact generic Spec_iff
  declaration at RingHomProperties.lean:360.
- rg of WeilConjectures and lean/Sheaf for
  "smooth_spec_iff|smooth_specMap_iff|HasRingHomProperty.Spec_iff" found uses of the
  generic comparison (including Smooth) but no separate specialized comparison.
- grep -rn of WeilConjectures for this node id returned no match.
- Read the complete HasRingHomProperty class, its ambient parameters, Spec_iff, and
  the Smooth instance directly in the pinned Mathlib source. Also searched the
  project's declaration-name index for the specialized names: no match.

Validation: scompile.py compiled scratchpad/Check.lean on the server cleanly in 1.7 s.
The scratch file uses `set_option autoImplicit false` and an explicit universe u;
#check verifies the exact specialization with an explicit type annotation:
`∀ (R S : CommRingCat.{u}) (φ : R ⟶ S),
  Smooth (Spec.map φ) ↔ RingHom.Smooth φ.hom`.
It states no new theorem and is not a delivery module. No proof or definition was written.
No node correction, missing notion, unusable dependency, or disputed statement was found.

## Second reading by J1

I independently compared the node's objects and clauses with the recorded declaration. The node introduces a homomorphism of commutative rings \(\varphi:R\to S\), its contravariant affine morphism \(\operatorname{Spec}S\to\operatorname{Spec}R\), and the biconditional between smoothness of that morphism and smoothness of the ring map. The Lean rendering is `AlgebraicGeometry.HasRingHomProperty.Spec_iff`:
`P (Spec.map φ) ↔ Q φ.hom`, with `P := @AlgebraicGeometry.Smooth` and `Q := RingHom.Smooth`; the `HasRingHomProperty` instance is supplied by `Mathlib.AlgebraicGeometry.Morphisms.Smooth`. Thus `Spec.map φ` is exactly the induced morphism and `φ.hom` exactly the ring homomorphism. The dependency records identify `Smooth` with the node's locally-finitely-presented/formally-smooth notion (Stacks 02H6) and `RingHom.Smooth` with the recorded ring smoothness notion, including finite presentation, cotangent H1 vanishing, and finite-projective differentials. The equivalence has both directions and introduces no extra hypotheses.

I checked that the common universe `u` on `CommRingCat` is the declaration's universe and does not impose a mathematical restriction: any pair of rings can be lifted to a common universe. No Noetherian, finite-type, field, characteristic, nonzero, or flatness assumption is present. Zero rings, identity maps, polynomial maps, empty spectra, and arbitrary characteristics remain covered; the theorem does not quantify over test objects or an index set. The node's three dependencies are all used by the specialization: `Spec`/`Spec.map`, scheme `Smooth`, and ring `Smooth`. The existing declaration is therefore exact and no module or statement correction is needed.

Searches were rechecked in the pinned Mathlib and project sources: `rg` found the generic theorem at `Mathlib/AlgebraicGeometry/Morphisms/RingHomProperties.lean:360` and the `Smooth` instance at `Morphisms/Smooth.lean:73`; searches of `WeilConjectures/`, `lean/Sheaf/`, and the declaration index found no duplicate specialized theorem. The worker's scratch specialization compiled cleanly with `scompile.py`. I changed only the node's existing `lean` record (already present in this delivery) and added this independent reading; no mismatch was found.
