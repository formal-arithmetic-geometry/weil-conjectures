## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteTypeImageImmediateBoundaryPoint` states
`AlgebraicGeometry.finiteTypeImage_immediateBoundaryPoint`, with `sorry` as its
only proof. It defines no new notions. The informal statement is unchanged.
Source read: `literature/stacks-project/limits.tex`, Tag 0GWV, the paragraphs
starting “Assume S and Y affine” and “Denote T”, including the subsequent
stalk-dimension sentence. The current blueprint direct-images proof was also
read; this is the supporting universal-closedness tool specified by this DAG node.

The explicit structure morphisms `p` and `q` describe the two k-schemes. This is
the several-morphisms-over-a-base case allowed by the scheme-over-field convention.
All types and universes are bound explicitly, with `set_option autoImplicit false`.

Hypotheses and clauses, in their order:

- Field k: `(k : Type u) [Field k]`.
- Schemes X and Y: `(X Y : Scheme.{u})`; Y affine: `[IsAffine Y]`.
- X and Y locally of finite type over k: the structure morphisms `p` and `q`
  with `[LocallyOfFiniteType p] [LocallyOfFiniteType q]`.
- Quasi-compact k-morphism f: `(f : X ⟶ Y) [QuasiCompact f]` and
  `(hfk : f ≫ q = p)`. No separatedness, reducedness, or integrality of X or Y
  is assumed.
- Any closed subset Z: `(Z : Set X) (hZ : IsClosed Z)`.
- Its image is not closed: `(himage : ¬ IsClosed (f '' Z))`.
- The points y,t,x and f(x)=t: `∃ (y t : Y) (x : X) (hxt : f x = t)`.
- Membership x in Z: `x ∈ Z`.
- y closed: `IsClosed ({y} : Set Y)`.
- y in the closure but outside the image:
  `y ∈ closure (f '' Z) ∧ y ∉ f '' Z`.
- Immediate specialization: `t ≠ y ∧ t ⤳ y`, with
  `∀ z : Y, t ⤳ z → z ⤳ y → z = t ∨ z = y`.
  This quantifies over all intervening points of Y, not just points of T.
- Finite extension kappa(x)/kappa(t): `(f.residueFieldMap x).hom.Finite`.
  Mathlib `RingHom.Finite` is finite generation as a module for the algebra
  structure induced by that very ring map. Since both rings are fields and
  `hxt : f x = t`, this is exactly the required finite field extension.
- T with its reduced induced closed structure: the existential ideal sheaf I is
  fixed by `I = Scheme.IdealSheafData.vanishingIdeal
  ⟨closure ({t} : Set Y), isClosed_closure⟩`. Thus `I.subscheme` and
  `I.subschemeι` are the recorded reduced-induced construction on that precise
  closed set; I is not an arbitrary closed subscheme or a hollow definition.
- T integral and affine: `IsIntegral I.subscheme ∧ IsAffine I.subscheme`.
- T finite type over k: `LocallyOfFiniteType (I.subschemeι ≫ q)` and
  `QuasiCompact (I.subschemeι ≫ q)`, using the actual induced structure map.
- Generic point t: `tT : I.subscheme`, `htT : I.subschemeι tT = t`, and
  `IsGenericPoint tT (Set.univ : Set I.subscheme)`.
- y belongs to T and remains closed there: `yT : I.subscheme`,
  `I.subschemeι yT = y`, and `IsClosed ({yT} : Set I.subscheme)`.
- Local dimension one: `ringKrullDim (I.subscheme.presheaf.stalk yT) = 1`.
- The canonical Spec kappa(x) map has image x:
  `Set.range (X.fromSpecResidueField x) = {x}`.
- Its composite with f is the canonical map through t in T: the final equality
  uses `Spec.map` of the field homomorphism kappa(tT) → kappa(x), namely the
  inverse of `I.subschemeι.residueFieldMap tT`, followed by the canonical
  equality transport `Y.residueFieldCongr (htT.trans hxt.symm)`, followed by
  `f.residueFieldMap x`. This spectrum map is composed with
  `I.subscheme.fromSpecResidueField tT` and `I.subschemeι`.
  The inverse's `IsIso` argument is supplied explicitly by the recorded
  closed-immersion residue-field theorem. It is not an arbitrary factorization.

Dependency declarations read and used:

| Node | Module and declarations |
| --- | --- |
| def-weil-field | `Mathlib.Algebra.Field.Defs`: `Field` (available through the public Mathlib imports) |
| def-pc-scheme | `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`; affinity uses `IsAffine` from `Mathlib.AlgebraicGeometry.AffineScheme` |
| def-weil-finite-type-morphism | `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`; `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact` |
| def-weil-residue-field | `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`, `Scheme.Hom.residueFieldMap`, `Scheme.residueFieldCongr` |
| lem-weil-pbc-reduced-induced-closed-subscheme | `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`: `Scheme.IdealSheafData.reduced_induced_closed_subscheme`; its real construction is `Scheme.IdealSheafData.vanishingIdeal`, `subscheme`, `subschemeι` |
| def-pc-integral-scheme | `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral` |
| def-weil-pbc-krull-dimension-ring | `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim` |
| def-pc-scheme-fibre | `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`; its canonical field-valued map is `Scheme.fromSpecResidueField`, from the public residue-field import |
| lem-weil-pbc-closed-immersion-residue-field-iso | `Sheaf.AlgebraicGeometry.ClosedImmersionResidueFieldIso`: `Scheme.Hom.isIso_residueFieldMap_of_isClosedImmersion` |

The last node was already a proof dependency and is now also added to
`stmt_deps`: the final formula uses its theorem as the explicit instance
argument of `CategoryTheory.inv`. Its existing declaration is usable; no
repair or duplicate declaration is supplied.

All already stated proof dependencies are imported, with public imports only
for the statement interface. In particular the non-Mathlib proof imports are
`WeilConjectures.Topology.ProconstructibleClosureSpecialization`,
`WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism`,
`Sheaf.AlgebraicGeometry.ClosedPointField`, and
`Sheaf.AlgebraicGeometry.FibreStalkQuotient`; their recorded declarations and
docstrings were read. The punctured-local-spectrum closed-point lemma currently
has no Lean record or Mathlib match, so there is no module to import for that
proof dependency. The statement does not require its declaration. All eight
natural-language proof steps, with their DAG inputs, are in the docstring.

Edge cases checked before writing:

- Empty X, empty Z, or empty Y makes the image closed, contradicting `himage`;
  no extra nonemptiness hypothesis is imposed.
- If the image is closed, the nonclosedness premise correctly excludes the case.
- For G_m → A¹, Z=X, take y=0 and t the generic point: the immediate
  specialization, finite residue extension, and dimension-one local ring hold.
- For G_m × A¹ → A¹, x need not be closed in X: one chooses a closed point of
  the generic fibre. The signature imposes no erroneous closedness on x.
- In higher dimension, T need not be globally one-dimensional. Only the local
  dimension at the chosen closed y is set to one, as the node says.
- Nilpotents and nonseparated source schemes are allowed. The reduced structure
  is imposed only on the closure T via its actual vanishing ideal.
- No characteristic restriction, algebraic closure, or perfectness of k appears.
- The field extension is for the induced residue-field map, not an independently
  chosen algebra structure. Finite inseparable extensions remain allowed.

Searches made for an existing statement:

- `msearch.py leanfinder`: “A nonclosed finite type scheme image has a missing
  closed boundary point and an immediate generalization in the image with finite
  residue field lift”. Eight hits, including `Scheme.range_fromSpecResidueField`,
  `isClosed_singleton_iff_locallyOfFiniteType`, `Scheme.Hom.coborderRange`, and
  `LocallyOfFiniteType.jacobsonSpace`. These provide individual constructions or
  inputs, not the combined selection and closure geometry.
- `msearch.py loogle`: `Specializes, AlgebraicGeometry.Scheme.Hom.residueFieldMap`.
  Zero hits.
- `msearch.py grep` in `AlgebraicGeometry`:
  `immediate.*special|boundary.*(finite|residue)|exists.*[Cc]losed.*[Ff]iber`.
  Zero hits.
- `msearch.py leansearch`: “A finite type scheme image has a missing closed
  boundary point with an immediate generalization in the image and a finite
  residue field lift”. Eight hits, including the closed-point image theorem,
  Jacobson fibres, residue fields, and finite morphisms. None states the item.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for immediate specializations,
  boundary/image combinations, and closure constructions found only component
  APIs, geometric specialization notions, and this item's consumer
  `NormalCurveUniversalClosednessTest`; no exact statement.
- `grep -rn` for the item's ID in `lean/WeilConjectures` returned no match.
  `rg` in `dag/lean_names_upstream.json` for the item ID and proposed declaration
  name returned no match.

No statement dispute, source correction, new node, or dependency module is needed.

Validation: `scompile.py Q135 lem-sfb-finite-type-image-immediate-boundary-point`
compiled the sandbox and final library module against the live server build,
with no errors or warnings. The first attempt identified the missing explicit
`IsIso` argument for `inv`; the final version uses the existing theorem rather
than declaring a new instance.

## Second reading by Q135

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
