# Formal Verification of Energy Rebound Effects

[![Open in GitHub Codespaces](https://github.com/codespaces/badge.svg)](https://codespaces.new/yourusername/formal-verification-rebound)

**→ Click the badge above to run proofs online - no installation required!**

## Running the Proofs

### Online (Recommended for Reviewers)
1. Click the Codespaces badge above
2. Wait for environment to load
3. Run `make` to compile all proofs
4. Open `.v` files in VS Code to explore interactively

### Local Installation
```bash
# Install Coq 8.17+, then:
git clone https://github.com/dhwcmoore/formal-verification-rebound
cd formal-verification-rebound
make
Files Structure
├── coq/                    # All Coq verification files
│   ├── EnergyEconomics.v   # Core economic framework
│   ├── WeiEquivalence.v    # Wei-Saunders equivalence proof
│   ├── ThresholdAnalysis.v # Rebound threshold conditions
│   ├── PolicyFramework.v   # Policy applications
│   └── Makefile           # Build configuration
└── README.md              # This file
Citation
If you use these formal proofs in your research:
bibtex@article{moore2025rebound,
  title={Formal Verification and the End of a Thirty-Year Controversy},
  author={Moore, Duston},
  journal={[Journal Name]},
  year={2025}
}