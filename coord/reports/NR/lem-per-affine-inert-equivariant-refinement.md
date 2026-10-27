## Worker report

The delivery states `AlgebraicGeometry.exists_affine_inert_equivariant_refinement`
in `Sheaf.AlgebraicGeometry.AffineInertEquivariantRefinement`. Its sole theorem
has proof `sorry`. There are no new definitions, new nodes, dependency repairs,
or statement changes. Only the item's `lean` record is added to its node.

The inherited BLOCKED ending was a stage-1 unchanged-node rejection. The live
node is split and reviewed by Q58, has no Lean record, and occurs in
`coord/queue.tsv` with stage 2. The handoff paragraph in `coord/brief-stage2.md`
§0 explicitly directs this stage-2 assignment to proceed with `deliver2.py`.
The accepted seven-step split is preserved verbatim.

Source read: ILO, Travaux de Gabber, VI 4.1, printed p.76 (PDF p.82), and
VIII 5.3.6--5.3.7, printed pp.124--125 (PDF pp.130--131). VI 4.1 identifies
geometric inertia by morphisms factoring through fixed subschemes. VIII 5.3.6
specifies inertia isomorphisms; proof 5.3.7 removes fixed loci and uses affine
invariant neighbourhoods. The node isolates the generic scheme localization
argument before rigidification, with the relative-etale equalizer argument
spelled out in its accepted proof. The current blueprint ancestor
`literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/sk-p-dl-a1-perverse/lem-per-artin-gabber-affine-curve`
(statement and proof files) was also read; the present helper serves its
recorded duality/purity route. No change to that blueprint unit is made.

Hypothesis and conclusion correspondence:

- Finite group: `{G : Type v} [Group G] [Finite G]`. No faithful action or
  invertibility assumption is present.
- Separated locally Noetherian scheme: `{X : Scheme.{u}} [X.IsSeparated]
  [IsLocallyNoetherian X]`. Quasi-compactness of X is not assumed.
- Action by scheme automorphisms: `ρX : G →* Aut X`. The group homomorphism
  laws give identity and composition. Mathlib's multiplication on `Aut X`
  satisfies `(ρX (g*h)).hom = (ρX h).hom ≫ (ρX g).hom`, precisely the
  usual left action convention in categorical composition order.
- Geometric point: `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]`
  and `x : Spec (.of Ω) ⟶ X`, following the dependency's inline interface.
- Exact subgroup H: `H : Subgroup G` with
  `hH : ∀ g : G, g ∈ H ↔ x ≫ (ρX g).hom = x`.
  H is thus the specified stabilizer, not an arbitrary smaller group.
- H-action on V: `{V : Scheme.{u}} (ρV : H →* Aut V)`.
- Equivariant etale map: `(f : V ⟶ X) [Etale f]` and
  `hf : ∀ h : H, (ρV h).hom ≫ f = f ≫ (ρX h.val).hom`.
- Marked fixed geometric point over x: `t : Spec (.of Ω) ⟶ V`,
  `ht : t ≫ f = x`, and `ht_fixed : ∀ h : H, t ≫ (ρV h).hom = t`.
- Prescribed invariant open containing the point: `(O : V.Opens)`,
  `htO : t default ∈ O`, and
  `hO : ∀ (h : H) (p : V), (ρV h).hom p ∈ O ↔ p ∈ O`.
  `Spec Ω` has its unique point as `default`; thus this is precisely
  containment of the image of the geometric point. The two-way membership
  condition is invariance under each automorphism.
- Affine Noetherian output: existential `W : Scheme.{u}` with
  `IsAffine W` and `IsNoetherian W`. These existential certificates impose
  the actual conditions on the output, without extra input hypotheses.
- H-action and fixed geometric point on W: existential
  `ρW : H →* Aut W`, `w : Spec (.of Ω) ⟶ W`, and
  `∀ h : H, w ≫ (ρW h).hom = w`.
- Etale equivariant refinement: existential `a : W ⟶ V`, `Etale a`,
  and `∀ h : H, (ρW h).hom ≫ a = a ≫ (ρV h).hom`.
- Factorization through O: `∃ b : W ⟶ O.toScheme, b ≫ O.ι = a`.
- Marked point over the specified point of V: `w ≫ a = t`.
- All geometric stabilizers agree under inclusion: for every
  `(K : Type u) [Field K] [IsAlgClosed K] (z : Spec (.of K) ⟶ W)`
  and every `g : G`, the equivalence
  `z ≫ a ≫ f ≫ (ρX g).hom = z ≫ a ≫ f ↔
   ∃ h : H, h.val = g ∧ z ≫ (ρW h).hom = z`
  says that the stabilizer in G is exactly the image of the stabilizer in H.
  Inclusion of a subgroup is injective, so this is exactly the stated
  identification of groups. Both sides compare entire scheme morphisms,
  including the residue-field embeddings, rather than only ordinary points.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`; affine
  schemes and open subschemes use Mathlib's `IsAffine`, `Opens.toScheme`,
  and `Opens.ι`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper`, `IsSeparated`, and `UniversallyClosed` were
  read; only separatedness is required here, represented by
  `AlgebraicGeometry.Scheme.IsSeparated` from the imported separated API.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`; output Noetherianity is
  `AlgebraicGeometry.IsNoetherian` in that module.
- `def-weil-geometric-point`: `Mathlib.FieldTheory.IsAlgClosed.Basic`,
  `IsAlgClosed` and its recorded inline field-spectrum morphism interface.
  The accompanying `Scheme.SpecToEquivOfField` in
  `Mathlib.AlgebraicGeometry.ResidueField` was read and confirms the
  ordinary-point plus residue-embedding interpretation; no alternative
  geometric-point definition is introduced.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale` (the current name, avoiding deprecated `IsEtale`).
- Group actions use `CategoryTheory.Aut` and its group structure in
  `Mathlib.CategoryTheory.Endomorphism`, and `Subgroup` in
  `Mathlib.Algebra.Group.Subgroup.Defs`. No private notion is needed.

All recorded proof-dependency modules are imported: Proper and Etale are public
statement imports; Noetherian supplies both pqf lemmas; ClosedImmersion,
OpenImmersion, AffineScheme, Morphisms.Affine, and
`Sheaf.AlgebraicGeometry.UnramifiedMorphism` are plain proof imports.
These cover base change of closed/open immersions, affine-open bases,
separated affine sources and affine intersections, open-immersion etaleness,
and locally Noetherian finite-type permanence.

Edge cases checked: trivial and nonfaithful groups are allowed; the identity
always belongs to H, so the finite intersections in the proof are nonempty
families. X need not be quasi-compact; V need not be separated. The second
affine shrinking in the accepted proof is retained to handle the latter.
All characteristics are allowed; no roots of unity or tameness is assumed.
Empty X or V admits no stipulated field-spectrum point, so these cases have
no input instance rather than producing an empty pointed output. Nonreduced
schemes and fixed loci remain allowed: equality on geometric-point morphisms
matches their field-valued functor, and the proof uses the reduced source
spectrum only when passing from image containment to factorization.
The scheme and geometric-field universes follow the dependency's `Scheme.{u}`
/ `Type u` convention; group size is independent (`v`). The conclusion does
not strengthen the requested etale map to an open immersion, though that
is how the accepted proof constructs it. No hypothesis is a tautological
replacement for a substantive condition.

Searches for an existing declaration, all with `msearch.py NR
lem-per-affine-inert-equivariant-refinement` on 2026-10-24:

- leanfinder: `An equivariant etale neighbourhood of a fixed geometric point
  admits an affine inert refinement preserving geometric stabilizers`:
  eight hits, all ordinary etale morphisms/sites (including `Scheme.Etale`,
  old-name `IsEtale` and stability under base change); no refinement theorem.
- loogle: `"Aut", "stabilizer"`: zero hits.
- grep in Mathlib AlgebraicGeometry:
  `([Ii]nert|[Ss]tabilizer).*(etale|étale|[Nn]eighbo)|[Ee]quivariant.*[Nn]eighbo`:
  zero hits.
- leansearch: `An equivariant etale neighbourhood of a fixed geometric point
  admits an affine inert refinement preserving all geometric stabilizers`:
  eight hits about etale algebra transport, etale pretopologies, a set-action
  stabilizer intersection, and Galois-category neighbourhoods; none assert
  the scheme refinement statement.
- `rg` in the project's `lean/WeilConjectures` and `lean/Sheaf` for the item id
  and action/stabilizer/invariant-affine-neighbourhood patterns: no existing
  declaration of this item. The upstream `InvariantAffineNeighbourhoods`
  theorem was read; it is a finite locally free descent-datum theorem with
  an orbit-affine hypothesis, so does not supply this statement. The log
  `PointwiseDiagonalKummerModel.inertia` uses the same membership-equivalence
  formulation but has different objects and hypotheses. Scheme action
  notation in `SchemeActionFixedIdeal` and `FSLogGroupAction.baseAction`
  already uses `G →* Aut X`, confirming reuse of the existing notion.
- The chosen full declaration name was searched in Mathlib,
  `lean/WeilConjectures` and `lean/Sheaf`; no collision was found.

Validation: `scompile.py NR lem-per-affine-inert-equivariant-refinement`
compiled the delivered file in both sandbox and actual module modes against
the live server library (3.1 s and 4.1 s), without errors or extra warnings.
`set_option autoImplicit false` ensures every binder is explicit.

## Second reading by NR

This is the author's separate clause-by-clause second pass, not an independent
agent review (the dispatcher forbids starting agents; independent review is
performed by the maintainer). I reopened the node and complete module and
checked each binder and conjunction against the correspondence above. In
particular, H is exactly the morphism stabilizer; the action on X is restricted
by `h.val`; O-invariance is bidirectional; the marked point lies over t itself;
all geometric fields K are quantified; and the final equivalence includes
membership in H as well as fixedness in W. The result assumes no separation
of V or action faithfulness, and concludes an etale map rather than imposing
an additional open-immersion clause. No mismatch was found and no statement
correction was needed.
