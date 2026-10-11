## Worker report

The module defines `CochainComplex.telescopeShift` and
`CochainComplex.telescopeToColimit` in full, and states
`CochainComplex.quasiIso_telescopeColimit`; its proof is `sorry`.
It uses the existing Mathlib coproduct, mapping cone, colimit, and quasi-isomorphism.

Statement correspondence:

- A site is `{C : Type u} [Category.{u} C] {J : GrothendieckTopology C}`.
- A sheaf of commutative rings is `R : Sheaf J CommRingCat.{u}`. Its underlying
  ring sheaf is `(sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R`.
- The sequence of cochain complexes of its module sheaves is the functor `E : ℕ ⥤
  CochainComplex (SheafOfModules ... ) ℤ`. The successor arrow is
  `E.map (homOfLE (Nat.le_succ n))`; using a functor records all transition maps.
- The direct sum is `∐ (fun n : ℕ => E.obj n)`. The endomorphism
  `telescopeShift R E` is `Sigma.desc` of each injection minus the successor
  transition followed by the next injection. Thus it is exactly `1 - shift`.
- `mappingCone (telescopeShift R E)` is the cone defining the telescope. `colimit E` is the
  termwise filtered colimit by Mathlib's `HomologicalComplex` colimit instance.
- `telescopeToColimit R E := Sigma.desc (fun n => colimit.ι E n)` is the canonical map from the
  direct sum to the colimit. The stated `f` is characterized as its extension
  from the cone: `mappingCone.inr (telescopeShift R E) ≫ f = telescopeToColimit R E`
  and its shifted component is zero,
  `(mappingCone.inl (telescopeShift R E)).comp (Cochain.ofHom f) (add_zero _) = 0`.
- `QuasiIso f` says every cohomology sheaf map is an isomorphism.

Dependencies: `CochainComplex` from
`Mathlib.Algebra.Homology.HomologicalComplex` for
`def-pc-cochain-complex-modules`, and `QuasiIso` from
`Mathlib.Algebra.Homology.QuasiIso` for `def-pc-quasi-iso-modules`.
The cone API comes from `Mathlib.Algebra.Homology.HomotopyCategory.MappingCone`;
`Sigma.desc` and `Sigma.ι` come from `Mathlib.CategoryTheory.Limits.Shapes.Products`.

Edge cases: the first successor at `n = 0` is included; zero complexes and
zero transition maps remain allowed. No nonemptiness condition is placed on
the site. The index is all of `ℕ`, so the theorem does not accidentally exclude
any stage of the sequence. The relevant Stacks result is Derived Categories,
Lemma 0949 (read at `/home/ubuntu/c1-stacks-review/derived.tex`); the node's
`sites-cohomology.tex` Lemma 06YS source field points to the K-flat resolution
application rather than the actual telescope argument.

Searches: `msearch.py` leanfinder, query "homotopy colimit of a sequence of
complexes of sheaves is quasi-isomorphic to the termwise filtered colimit":
eight related results, no telescope theorem. `msearch.py` loogle, query
"CochainComplex.mappingCone.descShortComplex, QuasiIso, Sigma.desc": no match.
`msearch.py` grep, query `hocolim|homotopyColimit|telescope|colim_hocolim`
under `Algebra/Homology`: no match. `rg` in `WeilConjectures` and `lean/Sheaf`
for telescope/hocolim/colimit with mappingCone found no matching statement;
`grep -rn lem-pc-complex-hocolim-colimit` in `WeilConjectures` found none.
Mathlib has `mappingCone.descShortComplex` for an arbitrary short exact
complex, but no telescope-specific statement or construction of `1 - shift`.

## Second reading by K1

- Site: `{C : Type u} [Category.{u} C] {J : GrothendieckTopology C}` is the
  site in the node. Verdict: matches the small-site convention used by the
  sheaf-module instances; no nonemptiness or separation assumption is added.
- Ring sheaf: `R : Sheaf J CommRingCat.{u}`, transported by `sheafCompose J
  (forget₂ CommRingCat.{u} RingCat.{u})` to the ring sheaf used by
  `SheafOfModules.{u}`. Verdict: the same commutative ring sheaf, with no field,
  characteristic, or Noetherian assumption.
- Sequence: `E : ℕ ⥤ CochainComplex (SheafOfModules ... ) ℤ`; its successor map
  is `E.map (homOfLE (Nat.le_succ n))`. Verdict: the node's cochain complexes,
  module category, integer degrees, and compatible transition maps.
- Direct sum and `1 - shift`: `∐ (fun n : ℕ => E.obj n)` and
  `telescopeShift R E`, whose `Sigma.desc` component is the injection at `n`
  minus the successor map followed by the injection at `n + 1`. Verdict:
  matches the node, including the sign and every stage starting at zero.
- Homotopy colimit: `mappingCone (telescopeShift R E)`. Mathlib's cone has the
  source shifted in its first component and the target in its second, as in
  the node's proof. Verdict: matches.
- Filtered colimit: `colimit E`; `HomologicalComplex` colimits are computed
  degreewise. Verdict: the node's termwise filtered colimit.
- Canonical map: `f` restricts to `telescopeToColimit R E` on
  `mappingCone.inr` and to zero on the shifted component `mappingCone.inl`.
  These two components characterize the projection to the colimit, so the
  existential formulation states the canonical map. Verdict: matches.
- Conclusion: `QuasiIso f` means that every integer-indexed cohomology map
  is an isomorphism. Verdict: matches the node, with no stronger conclusion.

Dependency checks: `def-pc-cochain-complex-modules` records Mathlib's
`CochainComplex`, specialized to the same sheaf-module category; the abelian
instance is available there. `def-pc-quasi-iso-modules` records Mathlib's
`QuasiIso`, equivalent to isomorphisms on all cohomology objects. Neither is a
private replacement or a narrower notion. There are no new definition nodes
or dependency modules in this delivery.

Edge cases: `ℕ` includes `0`; zero complexes, zero maps, the empty site, and
the empty scheme when represented by its site remain allowed. No characteristic
is fixed. The shared universe `u` is the small-site setting supported by the
sheaf-module instances and does not require the site to have an object.

Independent searches: `msearch.py` leanfinder for “homotopy colimit mapping
cone of one minus shift quasi isomorphic to colimit of complexes” returned
related mapping-cone quasi-isomorphisms, but no telescope theorem. Loogle for
`mappingCone, colimit, QuasiIso` returned no result (it did not resolve the
unqualified mapping-cone name). `msearch.py` grep for
`homotopyColimit|hocolim|telescope|mappingCone.*colimit` found no relevant
homological declaration. `rg` over Mathlib homology, `WeilConjectures`, and
`lean/Sheaf` found no matching telescope comparison. The source's Stacks
Derived Categories, Lemma 0949, assumes exact sequential colimits in an
abelian category; the chosen sheaf-module category has the requisite
filtered-colimit construction, and the node specializes that result.

Mismatch and change: none in the Lean or node. Replaced the pending second
reading placeholder with this source, dependency, and signature audit.
