## Worker report

The module `Sheaf.AlgebraicGeometry.IntegralFibreEtaleSplitting` states
`AlgebraicGeometry.exists_integral_fibre_etale_splitting`, with `sorry` as its entire proof.
No definitions or new nodes are introduced; the copied node changes only in `lean`.

Source read: literature/stacks-project/more-morphisms.tex, Tag 0BSR,
label lemma-etale-makes-integral-split, lines 12211–12309, including both proofs.
The node explicitly specializes that source to finite residue extensions; the source permits
an infinite purely inseparable part. The delivered statement keeps the node's stronger
hypothesis, without requiring finite type or a Noetherian base.

Hypothesis and clause correspondence:

- Affine schemes T and S: `{T S : Scheme.{u}} [IsAffine T] [IsAffine S]`.
- The integral morphism: `(π : T ⟶ S) [IsIntegralHom π]`.
- A point of the base: `(s : S)`.
- Finitely many points in its fibre: `Set.Finite {b : T | π b = s}`. This is the
  topological inverse image, so no extra notion of scheme fibre is required in the signature.
- Finite-dimensional residue extensions at every fibre point: `hresidue` uses
  `(π.residueFieldMap b).hom.Finite` for every b with π b = s. RingHom.Finite is module
  finiteness for the algebra induced by that map. Its source is κ(π b), identified with κ(s)
  by the fibre equality. No arbitrary algebra structure is quantified over.
- Affine pointed étale neighbourhood: existential U, g, u, followed by
  `IsAffine U ∧ Etale g ∧ g u = s`.
- A nonnegative integer m: `m : ℕ`, with no positivity condition and no equation with the
  cardinality of the original fibre.
- Open subschemes of the base change: `V : Fin m → (pullback π g).Opens`; each carries its
  canonical inclusion `(V i).ι` and scheme `(V i).toScheme`.
- Closed and affine pieces: `IsClosed (V i : Set ↥(pullback π g))` and `IsAffineOpen (V i)`.
  Openness is already part of the type of V.
- Pairwise disjoint: `Pairwise (fun i j ↦ Disjoint (V i) (V j))`.
- Covering the whole pullback: `(⨆ i, V i) = ⊤`.
- The structure map of each piece is integral:
  `IsIntegralHom ((V i).ι ≫ pullback.snd π g)`.
- Exactly one point over u: a point v of `(V i).toScheme`, its image equal to u,
  and every w with image u equal to v. Neither existence nor uniqueness is omitted.
- Purely inseparable residue extension: `@IsPurelyInseparable` with the algebra
  `(((V i).ι ≫ pullback.snd π g).residueFieldMap v).hom.toAlgebra`.
  The written base is κ(image v), equal to κ(u) by the preceding conjunct. The residue
  field is that of the actual open subscheme, not a separately invented field.
- When m = 0 the empty supremum is bottom; the covering equation forces the pullback empty.

Dependency declarations read and used:

- def-weil-finite-integral-morphism: `AlgebraicGeometry.IsIntegralHom`,
  Mathlib.AlgebraicGeometry.Morphisms.Integral (the node's record explicitly names this
  declaration for its integral clause, alongside IsFinite for its finite clause).
- def-pc-scheme: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  Mathlib.AlgebraicGeometry.Scheme.
- def-weil-affine-spectrum: `AlgebraicGeometry.Spec` and `Spec.map`, same module.
  Their affineness notion is used through Mathlib's `IsAffine` / `IsAffineOpen`,
  Mathlib.AlgebraicGeometry.AffineScheme; no coordinate-ring presentation is chosen.
- def-weil-residue-field: `Scheme.residueField` and `Scheme.Hom.residueFieldMap`,
  Mathlib.AlgebraicGeometry.ResidueField.
- def-pc-field-extension: `Algebra`, Mathlib.Algebra.Algebra.Defs, instantiated by
  `RingHom.toAlgebra` for the canonical residue map.
- def-weil-etale-morphism: `AlgebraicGeometry.Etale`,
  Mathlib.AlgebraicGeometry.Morphisms.Etale.
- def-pc-fibre-product: `CategoryTheory.Limits.pullback` and `pullback.snd`,
  Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback; existence for schemes
  comes from Mathlib.AlgebraicGeometry.Pullbacks.
- def-weil-pbc-finite-purely-inseparable-extension: `IsPurelyInseparable`,
  Mathlib.FieldTheory.PurelyInseparable.Basic, and module finiteness expressed via
  RingHom.Finite in the hypothesis. The conclusion only asks purely inseparable, as the node does.

The two recorded non-Mathlib proof modules are imported privately:
Sheaf.AlgebraicGeometry.EtaleSplitResiduePoints
(`AlgebraicGeometry.exists_etale_split_residue_points`) and
Sheaf.RingTheory.LiftIdempotentUpstairs
(`AlgebraicGeometry.exists_etale_lift_isIdempotentElem`). Their signatures and docstrings
were read in the group clone. Mathlib proof inputs are privately imported from
OpenImmersion, Pullbacks, Fiber, Spectrum.Prime.Topology, Ideal.GoingUp, and
MorphismProperty.OverAdjunction; integral base-change stability is already available
through the public Integral import. The declaration docstring gives all eight DAG proof steps,
including clearing denominators, induction, orthogonalization and removal of the remainder.

Edge cases checked: empty T or empty fibre permits m = 0; an empty base has no point s
and hence no instance of the hypothesis. Nonempty fibres require every piece to meet the
marked fibre by the explicit existence clause. No characteristic restriction is imposed;
IsPurelyInseparable covers both characteristic zero and positive characteristic. Nilpotents,
non-Noetherian schemes, and integral morphisms that are not finite remain allowed.
The schemes use one arbitrary universe u, consistently with Scheme's morphism category.
All variables and universes are explicitly bound. No file-local notation or instances occur.

Searches actually run:

- msearch leanfinder: "An integral morphism of affine schemes with finite fibre splits after
  etale base change into affine clopen pieces with singleton purely inseparable fibres".
  Eight results; the closest is Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq,
  for a finite algebra and one prime. It does not give this integral affine-scheme statement.
- msearch loogle: "IsIntegralHom, Etale". Unknown identifier IsIntegralHom, zero hits.
- msearch leansearch: "integral morphism etale splitting finite fibre purely inseparable".
  Service unavailable (Internal Server Error); not counted as a negative mathematical result.
- msearch grep: "integral.*split|IsIntegralHom" in AlgebraicGeometry. Twenty-five hits:
  integrality definitions, stability and affine-space results, no exact splitting theorem.
- rg on upstream WeilConjectures and dag/lean_names_upstream.json for the node id and
  "integral.*split|etale.*integral": only unrelated standard-etale descent, normal-base
  and ramification declarations; no existing item declaration.
- rg in lean/Sheaf/AlgebraicGeometry for integral and étale splitting: existing isolated-point
  and quasi-finite-part splitting and EtaleSplitResiduePoints are related but do not state
  the full clopen covering of an arbitrary integral morphism here.
- rg for the chosen full declaration name in Mathlib, upstream WeilConjectures and
  lean/Sheaf found no collision before writing.

Validation: scompile.py compiled the initial statement cleanly after making the carrier
coercion in the closed-set annotation explicit. The final file includes the Mathlib proof
imports and is checked again by deliver2.py --no-push. No statement correction or disputed
clause is needed. The independent second reader has not yet reviewed this delivery.

## Second reading by NN

I independently read the node, all eight proof steps, the delivered module, Tag 0BSR
in more-morphisms.tex (including the section introduction and both proofs), and the
statement-dependency records and their actual declarations. Verdict: the Lean says
exactly what this node says. No mathematical or Lean repair was needed. Only this
second-reading section was added; the worker report remains above.

The source is an integral ring-map statement without a Noetherian, finite-type,
reducedness, or characteristic assumption. The node explicitly specializes its finite
separable-part hypothesis to finite-dimensional residue extensions and translates the
product of rings into a finite clopen affine decomposition. This is an intentional
specialization already present in the node, not an added Lean hypothesis. No
`statement_change`, new definition nodes, or dependency modules occur in this delivery.

Object, hypothesis, and conclusion inventory, with individual verdicts:

1. Two affine schemes T and S: `{T S : Scheme.{u}} [IsAffine T] [IsAffine S]`.
   Exact. Mathlib's IsAffine says the canonical map to Spec of global sections is an
   isomorphism. It does not impose finite generation or nonemptiness.
2. An integral scheme morphism π:T→S: `(π : T ⟶ S) [IsIntegralHom π]`.
   Exact. I read Integral.lean:35: affineness plus integral maps on affine-open
   sections. The integral clause of def-weil-finite-integral-morphism explicitly
   records this declaration; the finite clause IsFinite is not assumed here.
3. A chosen base point s: `(s : S)`. Exact; no geometric-point or closed-point
   restriction is introduced.
4. A finite set of points over s: `hfibre : Set.Finite {b : T | π b = s}`.
   Exact; no isolatedness or multiplicity condition is added. This uses the
   topological inverse image, precisely as the node does.
5. Every residue extension at those points is finite-dimensional:
   `hresidue : ∀ b : T, π b = s → (π.residueFieldMap b).hom.Finite`.
   Exact. I read RingHom.Finite in Finiteness/Defs.lean:170: it is Module.Finite
   for the canonical RingHom.toAlgebra. ResidueField.lean:123 gives source κ(π b)
   and target κ(b); the equality π b = s identifies the source with κ(s).
6. An affine scheme U, an étale map g:U→S, and u∈U above s:
   `∃ (U : Scheme.{u}) (g : U ⟶ S) (u : U), IsAffine U ∧ Etale g ∧ g u = s ∧ ...`.
   Exact. Etale.lean:41 is affine-local ring-map etaleness. No equality of κ(u)
   and κ(s), surjectivity of g, or elementary-neighbourhood assumption appears.
7. A nonnegative integer m: `∃ (m : ℕ) ...`. Exact; it is quantified after the
   neighbourhood, and is not forced to be the original fibre cardinality.
8. A finite family of open subschemes of T×_S U:
   `V : Fin m → (pullback π g).Opens`. Exact. The dependency's pullback is the
   categorical scheme fibre product, with second projection to U. I read
   Restrict.lean:46–52: `(V i).toScheme` is restriction to the open, and `(V i).ι`
   is its canonical inclusion. These are the actual open subschemes, not unrelated
   schemes equipped with unconstrained maps.
9. Each piece is closed and affine:
   `(∀ i, IsClosed (V i : Set ↥(pullback π g))) ∧ (∀ i, IsAffineOpen (V i))`.
   Exact; openness is carried by Opens. IsAffineOpen is IsAffine of the open
   subscheme (AffineScheme.lean:251).
10. The pieces are pairwise disjoint:
    `Pairwise (fun i j ↦ Disjoint (V i) (V j))`. Exact; different indices have
    empty intersection.
11. Their union is the whole base change: `(⨆ i, V i) = ⊤`. Exact, including
    the empty union. This is not a cover merely of the fibre or a neighbourhood
    inside the base change.
12. Every induced structure morphism V_i→U is integral:
    `∀ i, IsIntegralHom ((V i).ι ≫ pullback.snd π g) ∧ ...`. Exact orientation
    and property; no finiteness conclusion has replaced integrality.
13. Exactly one point v_i lies over u: `∃ v : (V i).toScheme`, followed by
    `((V i).ι ≫ pullback.snd π g) v = u` and
    `∀ w, ((V i).ι ≫ pullback.snd π g) w = u → w = v`. Exact: both existence
    and uniqueness occur for the same point used in the final clause.
14. Its residue extension over κ(u) is purely inseparable:
    `@IsPurelyInseparable (U.residueField (... v))
      ((V i).toScheme.residueField v) _ _ (...residueFieldMap v).hom.toAlgebra`.
    Exact. The preceding image equality identifies the first field with κ(u).
    I read the actual IsPurelyInseparable class, not just its name: it includes
    algebraicity and excludes nontrivial separable elements. Both rings here are
    fields by the residue-field instances. No freely chosen algebra structure or
    extra Module.Finite conclusion is introduced.

All recorded statement dependency notions are reused: Scheme/Spec, IsAffine,
IsIntegralHom, residueField/residueFieldMap, Algebra via RingHom.toAlgebra, Etale,
pullback/snd, IsPurelyInseparable and module finiteness. I opened the actual signatures
of these definitions, together with IsAffineOpen and the open-subscheme inclusion.
The existing proof imports EtaleSplitResiduePoints and LiftIdempotentUpstairs were
also opened. The former handles arbitrary morphisms and finite residue extensions
with finite lists of all points over each original point; the latter handles arbitrary
integral algebras and gives a quotient-preserving étale extension. Neither requires
finite type for the original integral map. They are existing dependencies, not new
modules of this delivery. The docstring tracks all eight node proof steps: residue
splitting, fibre-ring discreteness, clopen idempotents, denominator descent, successive
lifting, orthogonalization, affine integral pieces, and removal of the remainder.
The module and declaration docstrings carry the source and exact blueprint id.

Edge cases: Fin 0 is allowed, and its empty supremum equals bottom, so the covering
equation forces an empty pullback when m=0. An empty T or a point outside the closed
image is covered by this case; an empty S supplies no s. For m>0 each piece must have
its specified fibre point and so cannot be an empty piece. Nilpotents and zero
coordinate rings cause no exclusion. Characteristic zero and positive characteristic
are both allowed; purely inseparable in characteristic zero means a trivial field
extension. All schemes inhabit one arbitrary universe u, as in the dependency
scheme category; there is no independent smaller test-object universe. Every variable
and universe is bound. There is no local notation, private definition, hollow data,
extra theorem, or proved theorem: the sole proof is `by sorry`.

Independent duplicate searches (using different words from the worker):

- LeanFinder via msearch, query "An integral morphism decomposes after an etale
  neighbourhood into disjoint affine components with radicial singleton fibres":
  eight results, consisting of étale definitions/composition, affine-space integrality
  and normalization integrality; no matching decomposition theorem.
- Loogle via msearch, `IsPurelyInseparable, IsIdempotentElem`: successful, zero hits.
- LeanSearch via msearch, "Etale local decomposition of an integral morphism with
  finite fibre into affine pieces having one purely inseparable point": unavailable
  (Internal Server Error). This is a service failure, not evidence of absence.
- Direct rg across Mathlib AlgebraicGeometry and RingTheory/Etale, upstream
  WeilConjectures and project lean/Sheaf, with `integral.{0,50}(decompos|split)` and
  `etale.{0,35}(radicial|singleton)`, plus the full proposed declaration name:
  no matching statement. Related project hits concern finite primary decomposition,
  normal-ring decomposition, and singleton étale sites, not this theorem.
- I additionally opened Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq
  in Mathlib/RingTheory/Etale/QuasiFinite.lean:379. Its Algebra.FiniteType and
  Algebra.QuasiFiniteAt hypotheses and single chosen component make it unsuitable
  for this arbitrary integral morphism. The upstream name inventory had no integral
  splitting/decomposition match. Thus retaining this module is justified under H4.

Validation: the prescribed server scompile.py compiled the delivered file cleanly in
1.4 seconds, nice 19, two threads, 60-second limit. I also checked the node's
lean.statement against the file signature verbatim (equal), all lines against the
100-character limit (pass), and binders by eye. No mismatch was found and no source,
node statement, dependency, or Lean signature was changed.
