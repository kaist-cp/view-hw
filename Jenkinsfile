def setupRust() {
    sh "rustup component add rustfmt clippy"
    sh "rustup install nightly"
    sh "cargo update"
    sh "cargo"
}

pipeline {
    agent none

    stages {
        stage('Builds') {
            parallel {
                stage('Quick') {
                    agent {
                        docker {
                            image 'coqorg/coq:8.9.1'
                        }
                    }
                    steps {
                        sh "git submodule update --init"
                        sh "make -j"
                    }
                }
                stage('Full') {
                    agent {
                        docker {
                            image 'coqorg/coq:8.9.1'
                        }
                    }
                    steps {
                        sh "git submodule update --init"
                        sh "./build.sh"
                    }
                }
            }
        }
    }
}
