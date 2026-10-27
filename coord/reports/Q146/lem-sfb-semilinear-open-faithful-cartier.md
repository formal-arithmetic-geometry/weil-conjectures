## Worker report

The module `Sheaf.AlgebraicGeometry.SemilinearOpenFaithfulCartier` states
`AlgebraicGeometry.exists_semilinear_open_faithful_cartier` with proof `sorry`.
It also constructs the owning notion's canonical map
`AlgebraicGeometry.semilinearBaseChangeMap` by `pullback.map`. The compatibility
proof is composed entirely from `Category.comp_id`, `Category.id_comp`,
`AlgHom.comp_algebraMap`, congruence, and `Spec.map_comp`; neither data nor
well-definedness is postponed. Both declarations are recorded in `lean.declarations`.
No additional node, dependency repair, or statement correction is needed.
Only the item's `lean` field changes.

Sources read: the current blueprint's
`sec-six-functors-basics/sk-thm-sf-ctf-stability/`
`sk-thm-sf-ctf-stability-direct-images.proof.md`, clause (3);
ILO, Travaux de Gabber, X 2.3 Step 2, printed p.150 (PDF p.156), including the
decomposition subgroup acting on `(Y_0/S_0, Z_0 intersect Y_0)`; and
Stacks `divisors.tex`, `lemma-pullback-effective-Cartier-defined`, Tag 02OO,
case (6) and its proof. The module docstring contains the node's four-step proof.

Hypotheses, objects, and conclusions, clause by clause:

- Field `e`: `(e : Type u) [Field e]`. Field extension `L/e`:
  `(L : Type u) [Field L] [Algebra e L]`; its structural map is `algebraMap e L`.
- Subgroup of `Aut_e(L)`: `H : Subgroup (L ≃ₐ[e] L)`.
  There is no `Finite H`, `IsGalois`, separability, algebraicity or degree hypothesis.
- The e-scheme B is `B : Scheme.{u}` with `b : B ⟶ Spec (.of e)`.
  This is exactly the structure map of `Scheme.Over`, given explicitly instead
  of as an implicit class instance.
- `Y = B ×_e Spec L` is the standard
  `pullback b (Spec.map (CommRingCat.ofHom (algebraMap e L)))`.
  Its p and s are `pullback.fst` and `pullback.snd` with these arguments.
- The ambient `alpha_h = id_B × Spec(h⁻¹)` is
  `semilinearBaseChangeMap e L b h.val`, whose definition uses `pullback.map`
  with first map `𝟙 B`, second map
  `Spec.map (CommRingCat.ofHom h.val.symm.toRingHom)`, and base map `𝟙 _`.
  Thus the scalar map is the specified inverse, rather than an arbitrary map
  satisfying only a property on points.
- The open X is `U` of type `Y.Opens`; its actual open subscheme is `U.toScheme`
  with inclusion `U.ι`. Nonemptiness is `hne : Nonempty U.toScheme`.
- Stability is `hstable : ∀ h : H, U ≤ (semilinearBaseChangeMap e L b h.val) ⁻¹ᵁ U`.
  This states that every alpha_h maps U into U; since it is quantified also at
  h⁻¹, it is equivalent to invariance as a set, without adding a stronger assumption.
- The map u is always the actual composite `U.ι ≫ pullback.fst ...`.
  The flatness hypothesis is `[Flat (U.ι ≫ pullback.fst ...)]`, exactly as stated
  in the node. It is retained even though base change of a field extension is flat.
- The restricted left action is `∃ r : H →* Aut U.toScheme`.
  `Aut` consists of isomorphisms of schemes, including structure-sheaf maps;
  it does not mean permutations only of the underlying points.
  `Aut` multiplication is inverse to categorical composition:
  `(r (h*k)).hom = (r k).hom ≫ (r h).hom`. Together with `map_one` this is
  exactly the left-action identity r_h composed with r_k = r_(hk).
- The first conjunct `(r h).hom ≫ U.ι = U.ι ≫ semilinearBaseChangeMap ...`
  identifies each map as the restriction of the canonical alpha_h. Since `U.ι`
  is a mono, this characterizes it uniquely; no arbitrary action is substituted.
- The second conjunct is `(r h).hom ≫ U.ι ≫ pullback.fst ... =
  U.ι ≫ pullback.fst ...`, namely u composed with r_h = u.
  Composing this equation with b also states that these automorphisms are
  e-morphisms, for the inherited e-structure u composed with b.
- The third conjunct is the s_X formula, with
  `Spec.map (CommRingCat.ofHom h.val.symm.toRingHom)` on the right.
  In Lean's left-to-right composition it says
  r_h followed by s_X equals s_X followed by Spec(h⁻¹).
- Scheme faithfulness is the fourth conjunct
  `∀ h : H, (r h).hom = 𝟙 U.toScheme → h = 1`, the precise kernel condition
  requested by the node. Scalar faithfulness is the fifth conjunct
  `∀ h : H, (∀ a : L, h.val a = a) → h = 1` for the given evaluation action.
- An effective Cartier divisor is quantified through its ideal:
  `∀ I : B.IdealSheafData, I.IsInvertible → ...`.
  The recorded dependency's `IsInvertible` means a local single regular
  generator, not merely an abstract invertible module. `I.subscheme` with
  `I.subschemeι` is its effective closed subscheme D.
- Its actual pullback ideal J is the explicit expression
  `I.comap (U.ι ≫ pullback.fst ...)`, used throughout the final conjunct.
  Mathlib defines `comap` as `(pullback.fst u I.subschemeι).ker`, so this is
  literally the ideal of the fibre-product closed immersion. The existing
  `I.comapIso u` identifies the closed subscheme of this ideal with the
  fibre product, compatibly with its inclusion. There is no need to assert
  existence of a second ideal or repeat this already-defined comparison.
- The ideal formula J = u⁻¹I times O_X is also exactly this `comap`:
  the existing `ideal_comap_appLE` identifies its affine sections with
  `(I.ideal W).map (u.appLE W V h).hom`. Thus using this expression retains
  the requested scheme structure and the extended inverse-image ideal.
- Effectiveness of D_X is `(I.comap u).IsInvertible`.
- The support clause is the explicit set equality
  `((I.comap u).support : Set U.toScheme) = u ⁻¹' (I.support : Set B)`.
  Here `support` is the zero locus of the ideal, i.e. support of the divisor,
  as read in Mathlib's `IdealSheaf.Basic`; it is not the support of I as a module.
- Stability as a divisor is `∀ h : H, (I.comap u).comap (r h).hom = I.comap u`.
  This is equality of quasi-coherent ideal data (all affine-section ideals),
  exactly r_h⁻¹J times O_X = J, and includes all nilpotent scheme structure.
- Empty divisors are included: no condition excludes `I = ⊤`, the unit ideal.
  There are no assumptions on B or U of integrality, normality, properness,
  reducedness, finite type or nonempty divisor support.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (def-weil-field).
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, `algebraMap`
  (def-pc-field-extension), with `Mathlib.Algebra.Algebra.Equiv`/
  `Mathlib.FieldTheory.Galois.Basic` for e-algebra automorphisms and subgroups.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `Scheme.Hom`, `Spec`, `Spec.map`, `Spec.map_comp`
  (def-pc-scheme and def-weil-affine-spectrum).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `pullback`, `pullback.fst`, `pullback.snd`, `pullback.map`
  (def-pc-fibre-product); scheme pullbacks are supplied by the imported
  Mathlib scheme/ideal-sheaf interfaces.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`
  (def-weil-flat-morphism).
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`:
  `Scheme.IdealSheafData.IsInvertible` (def-nagata-effective-cartier-ideal)
  and `Scheme.IdealSheafData.IsInvertible.comap_of_flat`
  (lem-pc-flat-pullback-effective-cartier-ideal).
- `Mathlib.AlgebraicGeometry.Over`: `Scheme.Over`, `Scheme.Hom.IsOver`
  (def-weil-scheme-over-base), expressed by an explicit structure arrow
  and its commuting equation, using the recorded standard scheme category.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`
  (def-weil-open-immersion); `Mathlib.AlgebraicGeometry.Restrict`:
  `Scheme.Opens.toScheme`, `Scheme.Opens.ι`.
- `Mathlib.Geometry.RingedSpace.LocallyRingedSpace`:
  `LocallyRingedSpace.Hom`, with `RingedSpace` and `PresheafedSpace.Hom`
  (def-weil-locally-ringed-space-morphism).
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap` (def-weil-residue-field).
- `WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.PropertyC`:
  `Spec.residueFieldMap_residueFieldIso_hom`, with `Spec.map_apply` in
  Mathlib Scheme (lem-weil-pbc-spec-map-residue-field-naturality).
- Existing ideal interfaces, read in `Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`
  and `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine`:
  `comap`, `comapIso`, `support_comap`, `comap_comp`, `ideal_comap_appLE`.
  These notions are not redeclared.

Edge cases checked before writing: trivial H and identity extension L=e give
identity restrictions; the unit ideal gives the allowed empty divisor. Empty
X would destroy scheme faithfulness and is precisely excluded by hne. B may
have nilpotents and disconnected components; no step or binder excludes them.
Infinite or inseparable extensions are allowed, with arbitrary automorphism
subgroups. Nonemptiness is essential for the injection L into a residue field,
while flatness is the exact input needed for preservation of regular generators.
The common universe u is the ambient scheme/ring universe, arbitrary throughout;
there is no independent smaller test-object universe or finite-type restriction.

Searches for an existing statement (all made through msearch.py where applicable):

- LeanFinder: "A subgroup of field automorphisms acts faithfully on an invariant
  nonempty open of a scheme base change and preserves Cartier pullbacks".
  Eight hits: IsGaloisGroup fraction-ring/faithful results, fixed-point results,
  invariant algebras, and categorical Galois stabilizers; none gives this theorem.
- Loogle: `"AlgebraicGeometry", "FaithfulSMul"`: zero hits.
- Mathlib grep: `semilinear|FaithfulSMul|Cartier.*invariant|invariant.*Cartier`
  in AlgebraicGeometry: seven hits in ValuativeCriterion, EllipticCurve/Affine/Point,
  and StructureSheaf; these concern faithful modules or semilinear section maps.
- LeanSearch: "Nonempty invariant open subscheme of scalar extension has a faithful
  semilinear automorphism action with stable effective Cartier pullback".
  Eight hits, including `AlgEquiv.apply_faithfulSMul`, linear automorphism
  faithfulness, and Galois-field results. Scalar faithfulness is an ingredient;
  none supplies the scheme restriction and Cartier clauses.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for semilinear actions,
  scalar actions, subgroup/AlgEquiv signatures, and the item id; inspected
  `GaloisComponentPresentation` and `GaloisPointActionOpen`. The former is a
  consumer special case with finite Galois and proper integral assumptions,
  not a duplicate of this arbitrary-field-extension invariant-open lemma;
  the latter concerns open stabilizers of geometric etale lifts. The item id
  has no upstream Lean match. Searches for both proposed declaration names
  in Mathlib, WeilConjectures, Sheaf and dag/lean_names_upstream.json found none.

Validation: scompile.py compiled the delivered module separately as sandbox and
library against the published server build, cleanly (1.9 s and 2.0 s). All
variables and universe levels are explicitly bound; autoImplicit is false.
There is exactly one postponed theorem, the owning node's main statement.

## Second reading by Q146

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
