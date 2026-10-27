## Worker report

The module `Sheaf.AlgebraicGeometry.ClopenGenericProjectiveCover` states
`AlgebraicGeometry.clopen_generic_projective_cover`, with one postponed theorem and no
new definitions. Only the item's `lean` field changes. The mathematical statement and
its accepted seven-step proof split are preserved. No statement dispute or node fault
was found.

Sources read: the item's full statement and seven proof steps; every statement dependency's
statement and Lean record or Mathlib match; ILO X 2.3 Step 2, printed pp.150–151, especially
(2.c) (PDF pages 156–157); Stacks `properties.tex`, `lemma-normal-Noetherian`, Tag 033M,
lines 960–977; the current blueprint's `sk-thm-sf-ctf-stability-direct-images.proof.md`,
clause (3). The clopen-selection argument is the agent-extracted refinement recorded by
the node, rather than a verbatim assertion of the ILO text.

Hypothesis correspondence:

- Fields and finite extension: `e F : Type u`, `[Field e] [Field F]`, `[Algebra e F]`,
  `[Module.Finite e F]`. No separability or characteristic restriction is imposed.
- Prime: `ell : ℕ`, `hell : ell.Prime`.
- Scheme structures: `B X : Scheme.{u}`, `q : B ⟶ Spec (.of e)`,
  `p : X ⟶ Spec (.of F)`.
- Nonempty proper finite-type base: `[Nonempty B] [IsProper q]`. Properness includes
  `LocallyOfFiniteType q` and supplies `QuasiCompact q` through universal closedness,
  exactly as the recorded `def-weil-proper-morphism` explains. Thus the finite-type
  clause is retained without duplicate instance parameters. The first compile's
  overlapping-instance warning was repaired by removing these duplicate binders.
- Finite disjoint integral decomposition: `hB` supplies `n : ℕ` and opens `V : Fin n →
  B.Opens`, each `IsIntegral (V i).toScheme`, pairwise disjoint, whose supremum is top.
  Each open is also closed since its complement is the union of the remaining opens.
  This expresses the given finite disjoint union as actual open subschemes.
- Projective X over F: `[IsHProjective p]`, the recorded finite-projective-space
  convention. No projective-bundle replacement is made for this assumption.
- Normal X: `hnormal` gives `IsDomain` and `IsIntegrallyClosed` for every stalk,
  following the recorded inline normal-domain convention.
- The e-morphism: `d : X ⟶ B` and
  `hbase : d ≫ q = p ≫ Spec.map (CommRingCat.ofHom (algebraMap e F))`.
- Chosen generic points: `c : genericPoints B → genericPoints X` and
  `hc : ∀ b, d (c b).val = b.val`. Mathlib's `genericPoints` means that the singleton's
  closure is an irreducible component; `genericPoints.component` returns that closure,
  and `genericPoints.isGenericPoint` states the recorded `IsGenericPoint` property.
- Finite prime-to-ell residue degree at every chosen point: `hdegree` asserts
  `FieldExtension.degree ... = (n : WithTop ℕ)` and `n.Coprime ell`. The algebra
  argument is explicitly `(d.residueFieldMap (c b).val).hom.toAlgebra`, so the extension
  is induced by d, with no arbitrary scalar structure. Equality to a natural number
  forces the field extension to be finite: the recorded degree is top otherwise.
  Using the field at `d (c b).val` avoids an arbitrary transport across `hc`.

Conclusion correspondence, in conjunction order:

- `∃ U : X.Opens` and `(U : Set X) = ⋃ b, (genericPoints.component (c b)).val`
  specify exactly the selected union, with its canonical open subscheme structure.
  This existential is a proposition giving the stated open structure of that fixed set;
  it does not replace the selected set by an arbitrary suitable subscheme.
- `IsClopen (U : Set X)` gives openness and closedness.
- The stalkwise `IsDomain ∧ IsIntegrallyClosed` clause on `U.toScheme` gives normality.
- `IsHProjective (U.ι ≫ p)` gives projectivity over F.
- `∀ b : genericPoints B, ∃ x : U.toScheme, (U.ι ≫ d) x = b.val` states that every
  generic fibre is met.
- `IsHProjective (U.ι ≫ d)` and `IsProjectiveBundle (U.ι ≫ d)` give both required
  projectivity conventions for the actual restriction, and `Surjective (U.ι ≫ d)`
  gives surjectivity on points.
- For every `x ∈ genericPoints U.toScheme`, the image belongs to `genericPoints B`
  and the degree computed using `((U.ι ≫ d).residueFieldMap x).hom.toAlgebra` is a
  natural number coprime to ell. This uses the restricted scheme's own residue field,
  and therefore includes the restriction clause, not just the original degree assumption.
- `U.ι '' genericPoints U.toScheme = Set.range (fun b ↦ (c b).val)` states exactly the
  generic-point identification, with repetitions discarded by set range. All assumptions
  on residue degrees quantify only over c; omitted components have no degree condition.

Dependency declarations and source signatures read:

- `Mathlib.Algebra.Field.Defs`: `Field`; `Mathlib.Algebra.Algebra.Defs`: `Algebra`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`, whose parents are
  `IsSeparated`, `UniversallyClosed`, `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral`, with nonemptiness and domain
  section rings on nonempty opens.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `IsHProjective`, whose
  witness is a closed immersion into projective space on a finite coordinate type.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`, used
  together with `IsDomain` on the actual stalk rings.
- `Mathlib.Topology.Sober`: `IsGenericPoint`, `genericPoints`, `genericPoints.component`
  and `genericPoints.isGenericPoint`; `Mathlib.Topology.Irreducible`:
  `irreducibleComponents`, the maximal irreducible subsets.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and
  `Scheme.Hom.residueFieldMap`, with signature from the image point's field to the
  source point's field.
- `Sheaf.FieldTheory.FieldTower`: `FieldExtension.degree`, with explicit algebra
  instance, equal to finrank for a finite extension and top for an infinite one.
- `Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism`: `IsProjectiveBundle`, the
  canonical relative Proj of the symmetric algebra of a finite-type quasi-coherent module.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `Surjective`.

All recorded project proof modules needed by the accepted proof plan are imported:
`Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper` (full statement and proof
read) and `Sheaf.AlgebraicGeometry.RegularNormalDecomposition` (full statement and
proof read). Mathlib supplies the Noetherian, closed-immersion, open-immersion,
sobriety and closed-image tools. The proof-only
`lem-sfb-finite-constant-projective-graph` currently has no recorded declaration and
is therefore cited in the natural-language proof, without inventing an import or
stating an unneeded statement dependency. No missing notion or unusable interface
is needed to state this item.

Edge cases checked before writing: the identity over Spec e (degree 1); a finite disjoint
integral base; extra components of X whose maps have bad degree or nongeneric image
(they are simply omitted); inseparable F/e; ell equal to the characteristic (allowed);
zero-dimensional and positive-dimensional components. Empty B is explicitly excluded.
A decomposition indexed by Fin 0 cannot cover nonempty B. Empty X cannot carry the
required chosen generic points because nonempty B is covered by integral components,
which have generic points by sobriety. No independent small index universe can make a
hypothesis vacuous: the chosen family uses the actual set of generic points of B.
The same universe for the fields and schemes is the project's scheme convention;
arbitrary smaller objects may be lifted to a common ambient universe.

Searches actually run with the prescribed msearch wrapper (group N7, this item):

- `leanfinder`: “A union of selected irreducible components of a normal projective scheme
  is clopen and projectively surjects onto a proper base when its generic points cover
  the base”. Eight hits: Proj opens/properness and scheme sobriety, no exact theorem.
- `loogle`: `IsGenericPoint, IsClopen`. Zero hits.
- `grep`: `generic.*projective|projective.*generic|clopen.*component`, restricted to
  Mathlib AlgebraicGeometry. Zero hits.
- `leansearch`: “The selected generic irreducible components of a normal projective scheme
  form a clopen projective cover of a proper scheme”. Eight hits, including
  `genericPoints`, `genericPoints.component`, `genericPoints.ofComponent` and
  `finite_irreducibleComponents_of_isNoetherian`; no exact theorem. The existing
  generic-point/component interface is used, rather than copied.

Additional direct rg searches of both `lean/WeilConjectures` and `lean/Sheaf` for
`generic.*(clopen|projective)|clopen.*generic|clopen_generic_projective_cover` and the
item id found related generic-fibre lemmas and the larger
`semilinear_sylow_good_components`, whose stronger additional hypotheses and different
conclusions do not state this lemma. The latter's full signature and proof docstring
were read. Searching Mathlib, both project roots and `dag/lean_names_upstream.json`
for the chosen full declaration name found no collision. The exact item-id search
in upstream Lean also found no declaration.

Validation: every compiler call uses scompile.py and module mode. The initial compile
elaborated the theorem and reported only redundant finite-type instance binders; those
were removed. The final module is checked again by the server compiler and deliver2.py's
preflight and per-file compile. The only proof is `sorry`, as required for stage 2.

## Second reading by N7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
