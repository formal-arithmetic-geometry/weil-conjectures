## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleSplitsIsolatedPurelyInseparable` states
`AlgebraicGeometry.exists_etale_splits_isolated_purelyInseparable`, with proof exactly
`sorry`. It introduces no definitions. Only the item's `lean` record changes.

Source read: Stacks `more-morphisms.tex`, lines 12040–12168, especially Tag 02LO,
`lemma-etale-splits-off-quasi-finite-part-technical-variant`, its proof referring to
02LN and 02LM, and `morphisms.tex`, lines 8174–8210, Tag 02GL,
`lemma-etale-over-field`. The source provides precisely the node's splitting.
The finite separability of the neighbourhood residue extension follows from 02GL;
the finite purely inseparable residue extensions also include finiteness because
each piece is finite over the neighbourhood. The seven node proof steps appear in
the theorem's docstring, with their dependency IDs.

Hypotheses and clauses, checked individually:

- The size convention is an explicit `universe u`; `X`, `S`, and the existential
  neighbourhood `U` are all `Scheme.{u}`. There is no restriction on `u`. The larger
  metatheoretic universe requires no additional object or hypothesis in this theorem.
- The separated, locally finite type morphism is `(f : X ⟶ S) [IsSeparated f]
  [LocallyOfFiniteType f]`. There is no finite-type, quasi-compactness, Noetherian,
  flatness, reducedness, or characteristic assumption.
- The point and finite list are `(s : S) (n : ℕ) (x : Fin n → f.fiber s)`.
  `Function.Injective x` says the listed points are pairwise distinct;
  `∀ i, IsOpen ({x i} : Set (f.fiber s))` says exactly that they are isolated.
- `∃ (U : Scheme.{u}) (a : U ⟶ S) (u : U), Etale a ∧ ∃ (hu : a u = s), ...`
  is the pointed étale neighbourhood, including its required image equality.
- The canonical field map from `S.residueField s` to `U.residueField u` is
  `((S.residueFieldCongr hu.symm).hom ≫ a.residueFieldMap u).hom`.
  Its `RingHom.Finite` condition means finite dimension; the following explicitly
  instantiated `Algebra.IsSeparable` uses exactly this map's `toAlgebra`.
  `RingHom.Finite` is definitionally `Module.Finite` for `toAlgebra`
  (`Mathlib/RingTheory/Finiteness/Defs.lean:170–172`), so this uses the recorded
  finite-extension notion without a new definition or an arbitrary algebra structure.
- The nonnegative integers are `m : Fin n → ℕ`. The ambient base change is
  `pullback a f = U ×_S X`, in the order written in the node.
- `W` and `V i j` are opens of this base change, equipped with their actual induced
  open subschemes `W.toScheme`, `(V i j).toScheme` and canonical inclusions `.ι`.
  `IsCompl W (⨆ i, ⨆ j, V i j)` gives disjointness of `W` from the pieces and cover
  of the total scheme. `Pairwise (fun b c : (i : Fin n) × Fin (m i) ↦
  Disjoint (V b.1 b.2) (V c.1 c.2))` gives all pairwise disjointness of the pieces,
  including pieces belonging to different original points.
  Each `V i j` has the explicit `IsClosed` clause. `W` is closed because its
  complement is the displayed open union, by `IsCompl`. These are exactly the
  disjoint clopen subschemes in the displayed decomposition: a disjoint open cover
  with the restricted structure sheaves is the canonical scheme coproduct, not
  merely a bijection or a decomposition into arbitrary subsets. No extra choice
  of scheme structure is involved.
- `IsFinite ((V i j).ι ≫ pullback.fst a f)` states finiteness over `U`.
- `v i j : (V i j).toScheme` and its existential equality `hv` put the selected point
  over `u`; `∀ w, ... w = u → w = v i j` makes this fibre exactly a singleton.
- `((V i j).ι ≫ pullback.snd a f) (v i j) = f.fiberι s (x i)` says that it maps
  to the prescribed fibre point. This equality in `X` is equivalent to the
  node's equality in `X_s`: the canonical fibre map induced by the pointed residue
  extension commutes with projection to `X`, and `f.fiberι s` identifies `X_s`
  homeomorphically with `f⁻¹(s)` (`Scheme.Hom.fiberHomeo`). Thus there is no lost
  condition on the point or an unspecified map.
- The map for the residue extension of each singleton point is explicitly
  `((U.residueFieldCongr hv.symm).hom ≫
  ((V i j).ι ≫ pullback.fst a f).residueFieldMap (v i j)).hom`.
  `RingHom.Finite` and `@IsPurelyInseparable ... map.toAlgebra` express both clauses
  for this canonical extension. No local `let` or auxiliary field map is used.
- `∀ w : W.toScheme, (W.ι ≫ pullback.fst a f) w = u → ∀ i, ... ≠ f.fiberι s (x i)`
  is the complete avoidance assertion. As above, comparison after the injective
  projection of `X_s` is equivalent to comparison in that fibre.
- There is no finiteness condition on `W`; no flatness condition on `f`.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`, and its recorded
  separatedness notion `IsSeparated` (defined in `Morphisms.Separated`). Its proof
  interface `IsProper.of_comp` and finite-implies-proper instance are imported for
  node proof steps 3–4, as is separated base change.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`,
  `fiberToSpecResidueField`, `fiberHomeo`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`, `Scheme.residueFieldCongr`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`, also its composition,
  open-immersion and cancellation interfaces for proof step 5.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`; schemes have the required pullbacks.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`; the opens' `.toScheme`
  and `.ι` carry the canonical open-immersion structure.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`, including base-change
  permanence. These foundational modules are publicly available through the
  public imports `Fiber`, `Morphisms.Etale`, and `Morphisms.Proper`.
- `Mathlib.FieldTheory.PurelyInseparable.Basic`: `IsPurelyInseparable`;
  `Module.Finite` is used through its exact `RingHom.Finite` presentation.
- Private proof import `WeilConjectures.AlgebraicGeometry.EtaleLocalFiniteMultiplePoints`:
  `AlgebraicGeometry.exists_etale_local_finite_multiple_points`, the recorded
  upstream declaration of the 02LM proof dependency, whose full signature and
  proof-plan docstring were read.
- Private proof import `Mathlib.RingTheory.Unramified.LocalRing`: the recorded
  residue-field `Algebra.IsSeparable` and `Module.Finite` instances under
  `Algebra.IsUnramifiedAt`, for the affine residue-field argument in proof step 2.

Searches actually run with `msearch.py Q121 lem-sfb-etale-splits-isolated-purely-inseparable`:

- `leanfinder`: "Simultaneous etale splitting of isolated fibre points into finite
  clopen pieces with singleton purely inseparable special fibres". Eight results,
  including `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq` and
  `Algebra.Etale.iff_exists_algEquiv_prod`; no complete match. The former assumes
  a finite algebra, and the latter describes étale algebras over fields, whereas
  the theorem's morphism need not be étale, finite or flat.
- `loogle`: `"etale", "IsFinite"`. Three results, all `Algebra.IsFiniteSplit`
  instances or finite-étale tensor splitting, none stating the scheme result.
- `leansearch`: "Etale splitting of isolated fibre points into finite disjoint
  clopen schemes with purely inseparable singleton fibres". Eight results on
  étale field algebras, the étale locus and the étale scheme category; no match.
- `grep`, subdirectory `AlgebraicGeometry`: `02LO|exists_etale_isCompl|purelyInseparable|
  purely_inseparable`. The Zariski-main-theorem candidate
  `exists_etale_isCompl_of_quasiFiniteAt` only gives one finite clopen piece with
  a point above one original point. Its signature was read at
  `Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean:49–53`; it lacks singleton
  fibres, purely inseparable residues and simultaneous exhaustion.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the item ID and
  `etale.*[Ss]plit|etale.*[Ff]inite.*[Pp]oint`; `rg` in the upstream name inventory
  for `02LM|02LO|exists_etale_isCompl`, and full-name search in both roots and
  Mathlib. Existing 02LM, 02LN and 02LP modules were found and their relevant
  signatures read. The 02LM interface is a proof input without disjoint clopen
  pieces; 02LN requires an elementary neighbourhood and keeps the original
  residue fields, without the purely inseparable conclusion; 02LP splits the
  whole quasi-finite part without the labelled singleton-residue decomposition.
  None is the item, and the new theorem's full name was absent.

Edge cases checked before writing: `n = 0` makes the double union bottom and
`IsCompl W ⊥` forces `W = ⊤`; every indexed piece and avoidance clause is then
vacuous. A zero `m i` is syntactically allowed, as in the node (exhaustion and
avoidance force the mathematically required pieces). Several lifts of the same
original point are allowed and disjointness quantifies across all sigma indices.
There is no characteristic bound: in characteristic zero the recorded
`IsPurelyInseparable` means a trivial extension, and positive characteristic is
unrestricted. Nonreduced finite fibres are allowed because singleton conditions
concern points only. Empty `X` is allowed for an empty list; empty `S` has no `s`
and the theorem has no instances. No assumption of quasi-compactness on `X`, `S`
or `W` appears. The two residue-field equalities are used in the correct inverse
orientation, so the maps start at precisely `κ(s)` and `κ(u)`.

Validation: `scompile.py` compiles the delivered module as a sandbox module and
under its library name against the server's live published build, both clean
(1.6 s and 1.7 s). An initial ambiguity between type-category and scheme pullbacks
inside a `Set` annotation was repaired with explicit carrier coercion
`Set ↥(pullback a f)`. No additional hypotheses or declaration changes were needed.
No disputed statement or node fault was found.

## Second reading by Q121

I reopened the node, the final module, the full upstream 02LM signature, the
02LN/02LO source and the 02GL residue description. This is the author's second
reading; independent review is performed by the maintainer under the dispatcher's
instructions, and no other agent was started.

The binder `x : Fin n → f.fiber s` is the node's list of actual fibre points;
`hdistinct` and `hisolated` match its two separate conditions. The only morphism
hypotheses are separatedness and local finite type. I checked the conclusion in
order: the neighbourhood and its point, the finite separable canonical residue
extension, the natural-number multiplicities, the clopen partition, pairwise
disjointness over the full dependent sum, finiteness over `U`, existence and
uniqueness of each point over `u`, its image, both finite and purely inseparable
residue conditions, and every point of the complementary fibre avoiding every
listed point. The residue algebra structures use the actual projection maps,
with the equality transports in the right direction, rather than arbitrary
algebra structures. The apparent comparison in `X` loses no fibre information
because `fiberι` is injective. `IsCompl` in the lattice of opens supplies the
scheme decomposition with the induced structure sheaves, and forces `W` closed;
the remaining pieces also have explicit closedness clauses.

I checked the empty-list case by reducing both indexed suprema, the `m i = 0`
case, and nonreduced finite fibres. Nothing requires finite `W` or flat `f`.
No mathematical mismatch was found and no statement correction was made. The
only correction during elaboration was the explicit pullback-carrier coercion,
which does not change the statement. The stored signature is copied verbatim
from `theorem` to just before `:=`, and the JSON differs from the base only in
`lean`. There are no new nodes or dependency repairs.
