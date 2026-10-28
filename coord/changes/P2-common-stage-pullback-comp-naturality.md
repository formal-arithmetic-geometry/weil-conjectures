# Common-stage pullback compositor decomposition

The component construction and its `heq` API were moved into the new public module
`Sheaf.Paper.CommonStagePullbackCompComponent`; the item module publicly imports it.
This preserves the declarations and their signatures for existing users while allowing
finite-stage auxiliary statements to live below the naturality proof.

## Users

- `WeilConjectures.commonStagePullbackIntegralObject`
- `WeilConjectures.commonStagePullbackCompComponent`
- `WeilConjectures.commonStagePullbackCompComponent_heq`

The direct user `Sheaf.Paper.WeilIndSheafCategory` continues to receive these declarations
through the item's public import; no user source requires adaptation.
