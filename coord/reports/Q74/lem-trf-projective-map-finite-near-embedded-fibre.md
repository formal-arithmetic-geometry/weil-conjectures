## Worker report

The module `Sheaf.AlgebraicGeometry.ProjectiveMapFiniteNearEmbeddedFibre` states
`AlgebraicGeometry.ProjectiveSpace.exists_isFinite_restrict_near_embedded_fibre`.
Its only theorem has proof `sorry`; no definition or helper theorem is introduced.
The original node is unchanged except for its `lean` record.

The source read is `literature/stacks-project/coherent.tex`, Tag 0D2N,
`lemma-ample-in-neighbourhood`, especially lines 6154–6163: finiteness over a
neighbourhood of the projective fibre, then shrinking the base by closedness of
projective space. Although the surrounding ampleness lemma assumes a Noetherian
base, this final geometric argument works over an arbitrary base: its finite-fibre
input is the arbitrary-base Tag 02UP, already recorded by
`lem-trf-proper-finite-fibre-finite-near`. No statement correction is needed.

Hypotheses and clauses, in order:

- Schemes `S` and `Z`: `{S Z : Scheme.{u}}`, with explicit universe `u`.
- Projective dimension `r ≥ 0`: `(r : ℕ)`, including zero.
- `P = P^r_S` and its structural projection `q`: the existing
  `ℙ(ULift.{u} (Fin (r + 1)); S)` and `(ℙ(ULift.{u} (Fin (r + 1)); S) ↘ S)`.
  The coordinate type has exactly `r + 1` elements; ULift accommodates the
  scheme universe without changing its finite coordinate set. This is precisely
  the coordinate-index convention of `def-nagata-projective-space-base-change`.
- The proper map `φ : Z → P`: the binder `(φ : Z ⟶ ℙ(...; S))` and `[IsProper φ]`.
- The composite `f = q ∘ φ`: the explicit expression `φ ≫ (ℙ(...; S) ↘ S)`;
  no additional arbitrary structure morphism is introduced.
- The chosen base point: `(s : S)`.
- Scheme-theoretic fibres and the actual induced map `φ_s`: `pullback.map`
  from the pullback of `φ ≫ q` along `S.fromSpecResidueField s` to the pullback
  of `q` along that same map, induced by `φ`, the identity of `Spec κ(s)`, and
  the identity of `S`. By the existing definition of `Scheme.Hom.fiber`, these
  are exactly `(φ ≫ q).fiber s` and `q.fiber s`. The latter is the fibre model
  of projective space over `κ(s)`. The two `by simp` terms prove only the
  defining commutative squares for this canonical map.
- The hypothesis that `φ_s` is a closed immersion: `(hφs : IsClosedImmersion
  (pullback.map ...))`, with no arbitrary replacement map or extra properties.
- An affine open neighbourhood of `s`: `∃ V : S.Opens, s ∈ V ∧ IsAffineOpen V ∧ ...`.
- Finiteness of `φ_V`: `IsFinite (φ ∣_ (q ⁻¹ᵁ V))`. Mathlib's
  `morphismRestrict` has target `(q ⁻¹ᵁ V).toScheme` and source
  `(φ ⁻¹ᵁ (q ⁻¹ᵁ V)).toScheme`, hence exactly the open subschemes denoted
  `q⁻¹(V)` and `f⁻¹(V)` in the node. This is restriction of the original map.
- No Noetherian assumption, nonempty-fibre assumption, or fibre-surjectivity
  assumption appears in the signature.

Recorded dependency declarations read and used:

| Node | Module | Declaration/interface |
| --- | --- | --- |
| def-pc-scheme | Mathlib.AlgebraicGeometry.Scheme | AlgebraicGeometry.Scheme; Scheme.Hom |
| def-nagata-projective-space-base-change | WeilConjectures.AlgebraicGeometry.ProjectiveSpace | AlgebraicGeometry.ProjectiveSpace; ProjectiveSpace.over |
| def-weil-proper-morphism | Mathlib.AlgebraicGeometry.Morphisms.Proper | AlgebraicGeometry.IsProper |
| def-pc-scheme-fibre | Mathlib.AlgebraicGeometry.Fiber | AlgebraicGeometry.Scheme.Hom.fiber; fiberι; fiberToSpecResidueField |
| def-weil-closed-immersion | Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion | AlgebraicGeometry.IsClosedImmersion |
| def-weil-finite-integral-morphism | Mathlib.AlgebraicGeometry.Morphisms.Finite | AlgebraicGeometry.IsFinite |
| lem-trf-proper-finite-fibre-finite-near | Mathlib.AlgebraicGeometry.ZariskisMainTheorem | AlgebraicGeometry.exists_isFinite_morphismRestrict_of_finite_preimage_singleton |
| lem-weil-pbc-finite-local-on-target | Mathlib.AlgebraicGeometry.Morphisms.Basic | AlgebraicGeometry.HasAffineProperty.iff_of_iSup_eq_top; IsZariskiLocalAtTarget.iff_of_iSup_eq_top; IsZariskiLocalAtTarget.restrict |
| lemma-nagata-projective-space-base-change-proper | WeilConjectures.AlgebraicGeometry.ProjectiveSpace | AlgebraicGeometry.ProjectiveSpace.instIsProper |
| lem-weil-pbc-affine-opens-basis | Mathlib.AlgebraicGeometry.AffineScheme | AlgebraicGeometry.Scheme.isBasis_affineOpens |

The statement dependencies are public imports; the remaining proof-only modules
are plain imports. The module docstring and theorem docstring identify the source
and blueprint node; the theorem docstring includes all four DAG proof steps.
`set_option autoImplicit false` and the explicit universe binder prevent auto-bound
variables. There are no local definitions, local notation, or local instances.

Edge cases checked: `r = 0` gives one homogeneous coordinate; `Z_s` empty still
makes the pointwise fibres over `q⁻¹(s)` empty and the same closed-image argument
applies; `Z` empty is allowed; `S` empty has no possible supplied `s`, as intended.
A non-surjective closed immersion on the fibre is allowed, including points of
the projective fibre outside its image. Positive-dimensional embedded fibres,
nilpotents in either scheme, and non-Noetherian bases are not excluded. Finiteness
is asserted for `φ_V`, not for the map to `V`, so positive-dimensional `Z_s` is
consistent with the conclusion.

Searches performed with `msearch.py Q74 lem-trf-projective-map-finite-near-embedded-fibre`:

- LeanFinder: `A proper morphism to projective space whose base fibre is a closed
  immersion is finite near the base point`. Eight hits: properness of Proj,
  closed-immersion-implies-finite, the definition of finite, universal closedness
  of Proj, finiteness over a field, and local finite-type properties. No exact match.
- Loogle: `"IsProper", "IsFinite"`. Six hits: finite implies proper, proper plus
  affine iff finite, and proper plus locally quasi-finite iff finite. None states
  the relative projective-fibre neighbourhood conclusion.
- Mathlib grep: `exists_isFinite|IsFinite.*morphismRestrict|finite_near` in
  `AlgebraicGeometry`. Two hits in ZariskisMainTheorem.lean, lines 406 and 435:
  the existing pointwise finite-neighbourhood theorem and a use of it. The theorem
  is a proof dependency, not the whole item.
- LeanSearch: `Proper morphism to projective space with closed immersion on the
  fibre is finite over an open neighbourhood of the base point`. Eight hits:
  finite implies proper, closed immersion implies finite, finite iff finite and
  mono for closed immersions, and definitions/constructors. No exact match.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `finite_near_embedded|finiteNearEmbedded|finite.*near.*(embedded|closed)|projective_map_finite|lem-trf-projective-map-finite-near-embedded-fibre`:
  only unrelated finite-etale descent and quasi-finite chart material; no match.
  A broader `finite.*(projective|fibre|fiber)|projective.*finite` search was also
  inspected; the results concern other finiteness, projective modules, and
  cohomology, not this relative map statement. The literal node-id search found
  no upstream declaration.

No new nodes, dependency repairs, or statement disputes were necessary.

Validation: `scompile.py Q74 lem-trf-projective-map-finite-near-embedded-fibre`
compiled the delivered file successfully in both sandbox and library modes
(2.6 s and 1.6 s), with no errors or unexpected warnings.

## Second reading by Q74

The dispatcher's brief assigns the independent delivery review to the maintainer
and explicitly forbids starting other agents. This section records the author's
final rereading, not an independent-agent review.

Reread the node against the finished signature. `r : ℕ` and the lifted `r+1`
coordinate type match the classical projective dimension. The source of
`pullback.map` is the fibre of the composite, not the fibre of `φ` at a point of
projective space. Its target is the fibre of the projection; both base-change
along the same canonical residue-field morphism, and both identity components
are fixed. The closed-immersion hypothesis is imposed on that actual map.
The conclusion quantifies over an open of `S`, requires that it contain `s` and
be affine, and restricts `φ` over the inverse image of this open under `q`.
In particular it does not mistakenly require the composite to `V` to be finite.
No extra hypothesis, missing clause, or mismatch was found, and no change to
the mathematical statement was made.
