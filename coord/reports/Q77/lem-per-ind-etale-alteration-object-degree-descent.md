## Worker report

The module `Sheaf.AlgebraicGeometry.IndEtaleAlterationObjectDegreeDescent` states
`AlgebraicGeometry.PrimeToEllAlteration.exists_alteration_object_degree_stage` with
one `sorry`. It adds no definitions, helper theorems, new nodes, or dependency repairs.
Only the item's `lean` field changes. The signature is copied verbatim into that record.
The theorem docstring gives all eight proof steps of the accepted node.

### Hypotheses and conclusions

| Node clause | Lean rendering |
| --- | --- |
| Nonempty directed set I | `{I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]`. The index universe equals the schemes' universe, as prescribed for limits. |
| Inverse system of schemes S_a | `D : Iᵒᵖ ⥤ Scheme.{u}`. An inequality a₀ ≤ a gives `(homOfLE h).op : op a ⟶ op a₀`, in the required inverse direction. |
| Reduced affine Noetherian stages | The three pointwise instances `IsReduced (D.obj a)`, `IsAffine (D.obj a)`, and `IsNoetherian (D.obj a)`. The last is Mathlib's locally Noetherian and quasi-compact notion. |
| Affine etale transitions | Pointwise instances `IsAffineHom (D.map g)` and `Etale (D.map g)` for every arrow g. |
| All stages quasi-excellent | `_hqe : ∀ a : I, IsQuasiExcellent Γ(D.obj (op a), ⊤)`. For the assumed affine stages this is quasi-excellence of their coordinate rings, using exactly the dependency's predicate. |
| Reduced Noetherian inverse limit S | `c : Cone D`, `_hc : IsLimit c`, `[IsReduced c.pt] [IsNoetherian c.pt]`. No affineness or nonemptiness is imposed on c.pt. |
| Fixed initial stage | `a₀ : I`. |
| Prime ell invertible on S_a₀ | `ell : ℕ`, `[Fact ell.Prime]`, `_hell : IsUnit (ell : Γ(D.obj (op a₀), ⊤))`. Global invertibility is exactly invertibility on the affine scheme. |
| Finitely many initial schemes over S_a₀ | `n : ℕ`, `V : Fin n → Over (D.obj (op a₀))`. Any finite collection can be enumerated; repetition is harmless. |
| Each initial structure morphism finitely presented | For every b, `LocallyOfFinitePresentation (V b).hom`, `QuasiCompact (V b).hom`, `QuasiSeparated (V b).hom`. These are precisely the three clauses fixed by the conventions dependency (Stacks 01TP). |
| Finitely many specified morphisms between them | `m : ℕ`, `s t : Fin m → Fin n`, `f : ∀ j : Fin m, V (s j) ⟶ V (t j)`. These are actual S_a₀-morphisms, with no extra diagram relations. |
| Models V_b at the limit | `(Over.pullback (c.π.app (op a₀))).obj (V b)`. Mathlib's functor uses the ordinary scheme fibre product and its second projection, not a reduced fibre product in alt/S. |
| Every limit model is an object of alt/S | `_hV : ∀ b, ∃ T : Alt c.pt, T.obj = ...`. Equality is of the entire object in `Over c.pt`, including its structure morphism. This is membership in the dependency's full subcategory, not just existence of an unrelated isomorphic source scheme. |
| A common a₁ ≥ a₀ | `∃ (a₁ : I) (_ha₁ : a₀ ≤ a₁), ...`. |
| Every a ≥ a₁, every model is in alt/S_a | `∀ (a : I) (ha : a₁ ≤ a), (∀ b, ∃ T : Alt (D.obj (op a)), T.obj = (Over.pullback (D.map (homOfLE (_ha₁.trans ha)).op)).obj (V b)) ∧ ...`. |
| Selected good arrows stay maximally ell'-finite at every later stage | Second conjunct: for every j, the predicate `IsMaximallyPrimeToEllFinite ell` on `((Over.pullback (c.π.app (op a₀))).map (f j)).left` implies the identical predicate on the arrow pulled back along `D.map (homOfLE (_ha₁.trans ha)).op`. The implication selects exactly those specified arrows satisfying the limit condition; arrows not satisfying it are unrestricted. |
| Exact generic-point and residue-degree meanings | Reuses `Alt` and `IsMaximallyPrimeToEllFinite` from the recorded dependency. Unfolding `Alt` gives finite type, reduced source, component generic points mapping to component generic points, and finite induced residue-field homomorphisms. Unfolding the arrow predicate gives finite generic extensions and, for every target generic point in the image, a generic lift with coprime residue degree. For prime ell coprimality is exactly degree not divisible by ell. |
| Empty objects permitted | No `Nonempty` hypothesis on any scheme, no positive n or m condition. |
| No other geometric conclusions | The conclusion consists only of the object-membership conjunct and the degree-persistence conjunct. |

The witness `∃ T : Alt S, T.obj = X` uses the recorded category without introducing
a duplicate membership predicate: `Alt S` is the full subcategory for precisely the
node's condition, so such a witness is equivalent to that condition on X. Conversely
that condition constructs the witness with underlying object X and equality rfl.

### Dependency declarations used

- `Sheaf.AlgebraicGeometry.PrimeToEllAlterationTopology`:
  `AlgebraicGeometry.PrimeToEllAlteration.Alt` and
  `AlgebraicGeometry.PrimeToEllAlteration.IsMaximallyPrimeToEllFinite`.
  Their complete definitions and docstrings were read; no topology hypothesis is used.
- `Sheaf.RingTheory.ExcellentRing`: `IsQuasiExcellent`, with its Noetherian, G-ring,
  and open regular-locus clauses. The affine scheme's global ring supplies its argument.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced` (sectionwise).
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and `Spec.map`
  explain the affine-coordinate interpretation; the theorem keeps the given schemes
  instead of replacing them by independently chosen rings.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and
  `Scheme.Hom.residueFieldMap`, used inside the recorded alteration predicates.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`; the canonical functor `CategoryTheory.Over.pullback`
  is read from `Mathlib.CategoryTheory.Comma.Over.Pullback` and is used for every
  object's structure map and every arrow's base change.
- The conventions node fixes no declaration: finite presentation is written as its
  stipulated three Mathlib properties, with `Over` for schemes over a base.
- Limits use `Cone`, `IsLimit`, and the cone's actual projections; affine stages use
  `IsAffine` and Noetherian stages use `AlgebraicGeometry.IsNoetherian`.

The module has ordinary (non-public) imports of all recorded non-convention proof
modules, including the upstream affine-limit, filtered-colimit, reduced total-fraction,
etale reducedness, and finite / finite-locally-free descent declarations. The proof
nodes with no recorded declaration (the two total-fraction comparisons and the generic
fibre criterion) are not needed to type this statement and have no module to import.

### Edge cases and source reading

Checked the empty diagram of objects (`n = 0`, with `m = 0`), no specified arrows
(`m = 0`), an empty source, an empty target, and an empty limit. There is no exclusion
of the zero ring or empty schemes: generic-point quantifiers are vacuous there.
The same single a₁ works for all objects and all good arrows. The constant system
and a singleton directed index are included; a₁ may equal a₀. The degree predicate
checks target generic points only in the image, exactly as ILO II 1.1.8 requires.
The schemes need not be irreducible or separated. The initial objects are finitely
presented as morphisms, not merely locally finitely presented.

Read the local ILO PDF (pdftotext): II 1.1.8 and 1.2.2 fix the two predicates;
III 3.1(i),(iii), printed pp. 37--38, supply the finite-free generic rank method;
III 6.2 first paragraph, printed pp. 43--44, is the etale-limit context. This node
explicitly states an agent-formulated finite-stage interface, not the stronger
congruent-section approximation assertion. No source-based statement correction is
needed. No statement dispute or dependency fault was found.

### Searches

- `msearch.py ... leanfinder`: "Finite stage descent of reduced alteration objects
  and prime to ell generic degrees along inverse systems of affine etale schemes".
  Eight hits concerned generic affine-transition limit existence/equality of maps,
  etale algebras and finite factorization; none states the present object/degree descent.
- `msearch.py ... loogle`: "AlgebraicGeometry.PrimeToEllAlteration,
  IsMaximallyPrimeToEllFinite, Scheme.exists_isFinite_baseChange_stage".
  Zero hits, unknown identifier AlgebraicGeometry.PrimeToEllAlteration.
- `msearch.py ... grep`: "alteration|PrimeToEll|prime.to.ell" in AlgebraicGeometry.
  Zero Mathlib hits.
- `rg -n` for "alteration|PrimeToEll|prime.to.ell" in `lean/WeilConjectures`
  found only an unrelated use of alteration in a proof docstring.
  `grep -rn` for the item id in that directory found nothing.
- `rg -n` for "IsMaximallyPrimeToEllFinite|PrimeToEllAlteration.Alt" and related
  alteration terms in `lean/Sheaf` found the recorded topology module and unrelated
  alteration theorems; no existing finite-stage statement matching this node.

### Validation

`scompile.py Q77 lem-per-ind-etale-alteration-object-degree-descent <module>`
passed in both sandbox and library modes (1.7 seconds each), with no errors or warnings.
All variables and universes are explicit; `autoImplicit` is false. No proof was attempted.

## Second reading by Q77

A second pass by the same assigned worker (the dispatcher prohibits other agents)
compared the saved node and the complete compiled module. This is not represented as
an independent review; the maintainer's independent review remains the delivery review.

The inverse transition direction was checked explicitly: a₀ ≤ a gives an arrow from
op a to op a₀. The common stage precedes both conjuncts and the universal later-stage
quantifier, so object and degree descent occur simultaneously and persist everywhere
on the tail. The arrow conclusion is conditional separately for each specified arrow,
which allows arbitrary subsets of good arrows. Checking `Over.pullback`'s actual
implementation confirms that objects and arrows are their canonical scheme models.
The full-subcategory witness equates the whole over-object, preventing loss of the
structure morphism. Its predicate is exactly the one in the recorded `Alt` definition.

The three finite-presentation hypotheses, affine/quasi-excellent/reduced/Noetherian
base hypotheses, reduced Noetherian limit, prime and invertibility hypotheses, and
all empty cases are present. No properness, surjectivity, covering, regularity or
boundary condition was introduced. No mismatch was found and no statement changed.
